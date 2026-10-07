//! A units number written without its currency (`Assets:Foo  42.50`) takes
//! the currency beancount gives it (#2465).
//!
//! Each case is a row of the matrix checked against Python beancount 3.2.3
//! (`bean-check` plus `bean-query` for the booked postings). Beancount's rule,
//! from `booking_full.categorize_by_currency`: the one currency group the
//! other postings fall in when this is the only undetermined posting and it
//! carries no cost or price; otherwise the one currency the account already
//! holds; otherwise "Failed to categorize posting" / "Could not resolve units
//! currency".

use rustledger_booking::{BookingEngine, BookingError, InterpolationError};
use rustledger_core::{
    Amount, CostNumber, CostSpec, Decimal, IncompleteAmount, NaiveDate, Posting, PriceAnnotation,
    Transaction,
};
use std::str::FromStr;

fn dec(s: &str) -> Decimal {
    Decimal::from_str(s).expect("literal parses")
}

fn date(day: u32) -> NaiveDate {
    rustledger_core::naive_date(2026, 1, day).expect("valid date")
}

/// `account  <number> <currency>`.
fn amount(account: &str, number: &str, currency: &str) -> Posting {
    Posting::new(account, Amount::new(dec(number), currency))
}

/// `account  <number>`, the currency elided.
fn number(account: &str, number: &str) -> Posting {
    Posting::with_incomplete(account, IncompleteAmount::NumberOnly(dec(number)))
}

/// `{300 USD}`.
fn usd_cost() -> CostSpec {
    CostSpec::empty()
        .with_number(CostNumber::PerUnit { value: dec("300") })
        .with_currency("USD")
}

fn txn(day: u32, postings: Vec<Posting>) -> Transaction {
    postings.into_iter().fold(
        Transaction::new(date(day), "t"),
        Transaction::with_synthesized_posting,
    )
}

/// Book `history` (which must succeed), then `last`, returning the booked
/// postings of `last` as `(account, units)` strings, or the error.
fn book(history: Vec<Transaction>, last: Transaction) -> Result<Vec<String>, BookingError> {
    let mut engine = BookingEngine::new();
    for mut t in history {
        engine
            .book_interpolate_apply(&mut t)
            .expect("history books");
    }
    // Both public entry points must agree.
    let viewed = engine.book_and_interpolate(&last);
    let mut last = last;
    let applied = engine.book_interpolate_apply(&mut last);
    assert_eq!(
        viewed.is_ok(),
        applied.is_ok(),
        "book_and_interpolate and book_interpolate_apply disagree: {viewed:?} vs {applied:?}"
    );
    applied?;
    Ok(last
        .postings
        .iter()
        .map(|p| {
            let units = p.amount().expect("every posting booked");
            format!("{} {} {}", p.account, units.number, units.currency)
        })
        .collect())
}

fn cannot_infer(result: Result<Vec<String>, BookingError>) -> String {
    match result {
        Err(BookingError::Interpolation(InterpolationError::CannotInferCurrency { account })) => {
            account.to_string()
        }
        other => panic!("expected CannotInferCurrency, got {other:?}"),
    }
}

fn opening(day: u32, account: &str, n: &str, currency: &str) -> Transaction {
    txn(
        day,
        vec![
            amount(account, n, currency),
            Posting::auto("Equity:Opening"),
        ],
    )
}

/// The issue's ledger: the account holds only USD, and the other posting is
/// an auto-posting, so the balance is the only thing that can say. Beancount:
/// `42.50 USD` / `-42.50 USD`.
#[test]
fn currency_comes_from_the_accounts_single_currency_balance() {
    let got = book(
        vec![opening(2, "Assets:Foo", "100.00", "USD")],
        txn(
            3,
            vec![number("Assets:Foo", "42.50"), Posting::auto("Assets:Bar")],
        ),
    )
    .expect("beancount accepts this");
    assert_eq!(got, ["Assets:Foo 42.50 USD", "Assets:Bar -42.50 USD"]);
}

/// The other postings all fall in one currency: that one, with no history.
#[test]
fn currency_comes_from_the_one_other_currency_group() {
    let got = book(
        vec![],
        txn(
            3,
            vec![
                number("Assets:Foo", "42.50"),
                amount("Assets:Bar", "-42.50", "USD"),
            ],
        ),
    )
    .expect("beancount accepts this");
    assert_eq!(got, ["Assets:Foo 42.50 USD", "Assets:Bar -42.50 USD"]);
}

/// The other postings' group outranks the balance: Foo holds EUR, yet
/// beancount books `42.50 USD`.
#[test]
fn the_other_postings_group_outranks_the_balance() {
    let got = book(
        vec![opening(2, "Assets:Foo", "100.00", "EUR")],
        txn(
            3,
            vec![
                number("Assets:Foo", "42.50"),
                amount("Assets:Bar", "-42.50", "USD"),
            ],
        ),
    )
    .expect("beancount accepts this");
    assert_eq!(got, ["Assets:Foo 42.50 USD", "Assets:Bar -42.50 USD"]);
}

/// Two other groups: the group rule is out, the balance decides.
#[test]
fn two_other_groups_fall_back_to_the_balance() {
    let got = book(
        vec![opening(2, "Assets:Foo", "100.00", "USD")],
        txn(
            3,
            vec![
                number("Assets:Foo", "20.00"),
                amount("Assets:Bar", "-20.00", "USD"),
                amount("Assets:Baz", "-5", "EUR"),
                amount("Equity:Opening", "5", "EUR"),
            ],
        ),
    )
    .expect("beancount accepts this");
    assert_eq!(got[0], "Assets:Foo 20.00 USD");
}

/// Two other groups plus an auto-posting, the balance in a THIRD currency:
/// beancount books Foo in CAD and splits the auto-posting three ways.
#[test]
fn the_balance_currency_need_not_appear_elsewhere() {
    let got = book(
        vec![opening(2, "Assets:Foo", "100.00", "CAD")],
        txn(
            3,
            vec![
                number("Assets:Foo", "42.50"),
                amount("Assets:Bar", "-42.50", "USD"),
                amount("Assets:Baz", "3", "EUR"),
                Posting::auto("Equity:Opening"),
            ],
        ),
    )
    .expect("beancount accepts this");
    assert_eq!(got[0], "Assets:Foo 42.50 CAD");
    let mut rest = got[3..].to_vec();
    rest.sort();
    assert_eq!(
        rest,
        [
            "Equity:Opening -3 EUR",
            "Equity:Opening -42.50 CAD",
            "Equity:Opening 42.50 USD"
        ]
    );
}

/// Two currency-less postings, each read off its own account.
#[test]
fn several_postings_each_read_their_own_balance() {
    let got = book(
        vec![
            opening(2, "Assets:Foo", "100.00", "USD"),
            opening(2, "Assets:Bar", "100.00", "USD"),
        ],
        txn(
            3,
            vec![
                number("Assets:Foo", "42.50"),
                number("Assets:Bar", "-42.50"),
            ],
        ),
    )
    .expect("beancount accepts this");
    assert_eq!(got, ["Assets:Foo 42.50 USD", "Assets:Bar -42.50 USD"]);
}

/// A cost names the cost currency, not the commodity; the account holding
/// only HOOL says what is being sold. Beancount: `-5 HOOL {300 USD}`,
/// `1500 USD`.
#[test]
fn a_cost_bearing_posting_takes_the_commodity_the_account_holds() {
    let got = book(
        vec![txn(
            2,
            vec![
                amount("Assets:Foo", "10", "HOOL").with_cost(usd_cost()),
                Posting::auto("Equity:Opening"),
            ],
        )],
        txn(
            3,
            vec![
                number("Assets:Foo", "-5").with_cost(usd_cost()),
                Posting::auto("Assets:Bar"),
            ],
        ),
    )
    .expect("beancount accepts this");
    assert_eq!(got, ["Assets:Foo -5 HOOL", "Assets:Bar 1500 USD"]);
}

/// The same for a price: `-10 @ 1.2 USD` out of an EUR-only account.
#[test]
fn a_priced_posting_takes_the_currency_the_account_holds() {
    let got = book(
        vec![opening(2, "Assets:Foo", "100", "EUR")],
        txn(
            3,
            vec![
                number("Assets:Foo", "-10")
                    .with_price(PriceAnnotation::unit(Amount::new(dec("1.2"), "USD"))),
                Posting::auto("Assets:Bar"),
            ],
        ),
    )
    .expect("beancount accepts this");
    assert_eq!(got, ["Assets:Foo -10 EUR", "Assets:Bar 12.0 USD"]);
}

/// Nothing to read: no other group, an empty account. Beancount: "Failed to
/// categorize posting".
#[test]
fn an_empty_account_is_refused() {
    let got = book(
        vec![],
        txn(
            3,
            vec![number("Assets:Foo", "42.50"), Posting::auto("Assets:Bar")],
        ),
    );
    assert_eq!(cannot_infer(got), "Assets:Foo");
}

/// An account that held USD and was emptied holds nothing.
#[test]
fn an_emptied_account_is_refused() {
    let got = book(
        vec![
            opening(2, "Assets:Foo", "100.00", "USD"),
            opening(3, "Assets:Foo", "-100.00", "USD"),
        ],
        txn(
            4,
            vec![number("Assets:Foo", "42.50"), Posting::auto("Assets:Bar")],
        ),
    );
    assert_eq!(cannot_infer(got), "Assets:Foo");
}

/// Two currencies held: ambiguous, refused.
#[test]
fn an_account_holding_two_currencies_is_refused() {
    let got = book(
        vec![
            opening(2, "Assets:Foo", "100.00", "USD"),
            opening(2, "Assets:Foo", "100.00", "EUR"),
        ],
        txn(
            3,
            vec![number("Assets:Foo", "42.50"), Posting::auto("Assets:Bar")],
        ),
    );
    assert_eq!(cannot_infer(got), "Assets:Foo");
}

/// Two lots in different commodities, both at a USD cost: which one is being
/// sold is ambiguous. Beancount: "Could not resolve units currency".
#[test]
fn a_cost_bearing_posting_into_two_commodities_is_refused() {
    let lot = |c: &str| amount("Assets:Foo", "10", c).with_cost(usd_cost());
    let got = book(
        vec![txn(
            2,
            vec![lot("HOOL"), lot("AAPL"), Posting::auto("Equity:Opening")],
        )],
        txn(
            3,
            vec![
                number("Assets:Foo", "-5").with_cost(usd_cost()),
                Posting::auto("Assets:Bar"),
            ],
        ),
    );
    assert_eq!(cannot_infer(got), "Assets:Foo");
}

/// The residual is NOT a source. The other postings span USD and EUR and only
/// EUR is out of balance; the rule this replaced booked `5.00 EUR`, beancount
/// refuses ("Failed to categorize posting 4"), and so do we.
#[test]
fn the_residual_currency_is_not_read() {
    let got = book(
        vec![],
        txn(
            3,
            vec![
                amount("Assets:Foo", "100", "USD"),
                amount("Assets:Bar", "-100", "USD"),
                amount("Assets:Baz", "-5", "EUR"),
                number("Equity:Opening", "5.00"),
            ],
        ),
    );
    assert_eq!(cannot_infer(got), "Equity:Opening");
}

/// Another posting whose currency is still open — here a `{}` with no cost
/// currency — means this is not the ONLY undetermined posting, so the group
/// rule is out even though the other postings are all USD. Beancount: "Failed
/// to categorize posting 2" with an empty account; with Bar holding USD,
/// `1500.00 USD`.
#[test]
fn another_undetermined_posting_disables_the_group_rule() {
    let hool = || {
        txn(
            2,
            vec![
                amount("Assets:Foo", "10", "HOOL").with_cost(usd_cost()),
                Posting::auto("Equity:Opening"),
            ],
        )
    };
    let sale = || {
        txn(
            3,
            vec![
                amount("Assets:Foo", "-5", "HOOL").with_cost(CostSpec::empty()),
                number("Assets:Bar", "1500.00"),
                amount("Assets:Baz", "-10", "USD"),
                amount("Equity:Opening", "10", "USD"),
            ],
        )
    };
    assert_eq!(cannot_infer(book(vec![hool()], sale())), "Assets:Bar");

    let got = book(vec![hool(), opening(2, "Assets:Bar", "1", "USD")], sale())
        .expect("beancount accepts this");
    assert_eq!(got[1], "Assets:Bar 1500.00 USD");
}

/// A refused transaction is left exactly as written.
#[test]
fn a_refusal_leaves_the_transaction_untouched() {
    let mut engine = BookingEngine::new();
    let original = txn(
        3,
        vec![number("Assets:Foo", "42.50"), Posting::auto("Assets:Bar")],
    );
    let mut t = original.clone();
    assert!(engine.book_interpolate_apply(&mut t).is_err());
    assert_eq!(t, original);
}
