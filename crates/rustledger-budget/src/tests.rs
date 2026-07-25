//! Unit tests for the budget model.

use super::*;
use rustledger_core::naive_date;

fn d(y: i32, m: u32, day: u32) -> NaiveDate {
    naive_date(y, m, day).unwrap()
}

fn budget(from: NaiveDate, account: &str, interval: Interval, amount: i64) -> BudgetEntry {
    BudgetEntry {
        from,
        account: account.to_string(),
        interval,
        amount: Decimal::from(amount),
        currency: "USD".to_string(),
    }
}

/// Fava accepts both the bare noun and the `-ly` form of every interval,
/// case-insensitively — ten keywords, though its docs list only five.
#[test]
fn interval_parsing_accepts_all_ten_fava_keywords() {
    for (s, want) in [
        ("day", Interval::Day),
        ("daily", Interval::Day),
        ("week", Interval::Week),
        ("weekly", Interval::Week),
        ("month", Interval::Month),
        ("monthly", Interval::Month),
        ("quarter", Interval::Quarter),
        ("quarterly", Interval::Quarter),
        ("year", Interval::Year),
        ("yearly", Interval::Year),
    ] {
        assert_eq!(Interval::parse(s), Some(want), "keyword {s}");
        assert_eq!(
            Interval::parse(&s.to_uppercase()),
            Some(want),
            "case-insensitive {s}"
        );
    }
    assert_eq!(
        Interval::parse("fortnightly"),
        None,
        "unknown -> None, not a default"
    );
}

/// A whole calendar period accrues EXACTLY the stated amount — including
/// February, whose length differs between leap and common years. This is the
/// report's central promise: "my monthly budget is 400" must read 400.
#[test]
fn whole_period_accrues_the_exact_stated_amount() {
    let b = Budgets::new(vec![budget(
        d(2024, 1, 1),
        "Expenses:Food",
        Interval::Month,
        400,
    )]);
    // Leap February: 29 days.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 2, 1), d(2024, 3, 1))
            .unwrap(),
        Decimal::from(400),
        "29-day February still totals exactly the monthly amount"
    );
    // Common February: 28 days.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2025, 2, 1), d(2025, 3, 1))
            .unwrap(),
        Decimal::from(400)
    );
    // 31-day month.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2024, 2, 1))
            .unwrap(),
        Decimal::from(400)
    );
    // A whole year of a monthly budget is twelve months' worth.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2025, 1, 1))
            .unwrap(),
        Decimal::from(4800)
    );
}

/// An arbitrary partial window pro-rates by real calendar days: 14 of
/// February 2024's 29 days is 14/29 of the monthly figure.
#[test]
fn partial_window_prorates_by_calendar_days() {
    let b = Budgets::new(vec![budget(
        d(2024, 1, 1),
        "Expenses:Food",
        Interval::Month,
        400,
    )]);
    let got = b
        .accrue("Expenses:Food", "USD", d(2024, 2, 1), d(2024, 2, 15))
        .unwrap();
    let want = Decimal::from(400) * Decimal::from(14) / Decimal::from(29);
    assert_eq!(got, want);
    // Sanity: the fraction is a real 29-day denominator, not 28 or 30.
    assert!(
        got > Decimal::from(193) && got < Decimal::from(194),
        "got {got}"
    );
}

/// A later directive supersedes from its own date; a window spanning the
/// change picks up each rate for exactly the days it was in force.
#[test]
fn later_directive_supersedes_from_its_date() {
    let b = Budgets::new(vec![
        budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 400),
        budget(d(2024, 6, 1), "Expenses:Food", Interval::Month, 450),
    ]);
    // May (old rate) + June (new rate).
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 5, 1), d(2024, 7, 1))
            .unwrap(),
        Decimal::from(850)
    );
    // Whole year: Jan-May at 400, Jun-Dec at 450.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2025, 1, 1))
            .unwrap(),
        Decimal::from(5 * 400 + 7 * 450)
    );
}

/// Supersession is keyed on (account, CURRENCY): a second currency is a
/// parallel budget, not a replacement.
#[test]
fn currencies_coexist_rather_than_superseding() {
    let mut eur = budget(d(2024, 2, 1), "Expenses:Food", Interval::Month, 100);
    eur.currency = "EUR".to_string();
    let b = Budgets::new(vec![
        budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 400),
        eur,
    ]);
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 2, 1), d(2024, 3, 1))
            .unwrap(),
        Decimal::from(400),
        "the EUR entry must not supersede the USD one"
    );
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 3, 1), d(2024, 4, 1))
            .unwrap(),
        Decimal::from(400)
    );
    assert_eq!(
        b.accrue("Expenses:Food", "EUR", d(2024, 2, 1), d(2024, 3, 1))
            .unwrap(),
        Decimal::from(100)
    );
}

/// Days before the first declaration accrue nothing — a budget starts when it
/// is declared, it is not retroactive.
#[test]
fn nothing_accrues_before_the_first_declaration() {
    let b = Budgets::new(vec![budget(
        d(2024, 6, 1),
        "Expenses:Food",
        Interval::Month,
        300,
    )]);
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2024, 6, 1))
            .unwrap(),
        Decimal::ZERO
    );
    // A window straddling the declaration picks up only the covered part.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 5, 1), d(2024, 7, 1))
            .unwrap(),
        Decimal::from(300),
        "May accrues nothing; June accrues the full month"
    );
}

/// Weekly and yearly denominators are the real ones (7, and 365/366).
#[test]
fn weekly_and_yearly_denominators() {
    let w = Budgets::new(vec![budget(
        d(2024, 1, 1),
        "Expenses:T",
        Interval::Week,
        70,
    )]);
    // 29 days of February at 10/day.
    assert_eq!(
        w.accrue("Expenses:T", "USD", d(2024, 2, 1), d(2024, 3, 1))
            .unwrap(),
        Decimal::from(290)
    );
    let y = Budgets::new(vec![budget(
        d(2024, 1, 1),
        "Expenses:T",
        Interval::Year,
        3660,
    )]);
    // A whole leap year is exactly the yearly figure.
    assert_eq!(
        y.accrue("Expenses:T", "USD", d(2024, 1, 1), d(2025, 1, 1))
            .unwrap(),
        Decimal::from(3660)
    );
    // One day of a 366-day year.
    assert_eq!(
        y.accrue("Expenses:T", "USD", d(2024, 3, 1), d(2024, 3, 2))
            .unwrap(),
        Decimal::from(3660) / Decimal::from(366)
    );
}

/// Quarters anchor to Jan/Apr/Jul/Oct 1 — the calendar, not the directive date.
#[test]
fn quarters_anchor_to_calendar_boundaries() {
    assert_eq!(Interval::Quarter.start_of(d(2024, 5, 17)), d(2024, 4, 1));
    assert_eq!(Interval::Quarter.start_of(d(2024, 12, 31)), d(2024, 10, 1));
    // A budget declared mid-quarter still divides by the whole quarter's days.
    let b = Budgets::new(vec![budget(
        d(2024, 4, 1),
        "Expenses:T",
        Interval::Quarter,
        910,
    )]);
    assert_eq!(
        b.accrue("Expenses:T", "USD", d(2024, 4, 1), d(2024, 7, 1))
            .unwrap(),
        Decimal::from(910),
        "Q2 accrues exactly the quarterly amount"
    );
}

/// Weeks anchor to ISO Monday.
#[test]
fn weeks_anchor_to_iso_monday() {
    // 2024-03-07 is a Thursday; its ISO week began Monday 2024-03-04.
    assert_eq!(Interval::Week.start_of(d(2024, 3, 7)), d(2024, 3, 4));
    assert_eq!(Interval::Week.start_of(d(2024, 3, 4)), d(2024, 3, 4));
}
