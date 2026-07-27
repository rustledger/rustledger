//! Unit tests for the budget model.

use super::*;
use rustledger_core::naive_date;

fn d(y: i32, m: u32, day: u32) -> NaiveDate {
    naive_date(y, m, day).unwrap()
}

fn budget(from: NaiveDate, account: &str, interval: Interval, amount: i64) -> BudgetEntry {
    BudgetEntry {
        from,
        account: Account::new(account),
        interval,
        amount: Decimal::from(amount),
        currency: Currency::new("USD"),
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
    eur.currency = Currency::new("EUR");
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

/// The published ordering contract: `new` sorts by date STABLY, and supersession
/// takes the last entry on a date, so two declarations sharing a date and
/// `(account, currency)` supersede in the order the caller passed them.
///
/// This is the contract a non-CLI consumer most easily gets wrong, and it was
/// documented incorrectly ("entries need not be sorted", with no mention that
/// order decides the winner) until this test was written.
#[test]
fn same_date_entries_supersede_in_caller_order() {
    let first = budget(d(2024, 3, 12), "Expenses:Rent", Interval::Year, 3867);
    let second = budget(d(2024, 3, 12), "Expenses:Rent", Interval::Month, 3174);

    let as_written = Budgets::new(vec![first.clone(), second.clone()]);
    assert_eq!(
        as_written
            .in_force("Expenses:Rent", "USD", d(2024, 4, 1))
            .map(|b| b.interval),
        Some(Interval::Month),
        "the later line wins"
    );

    // Reversing the input reverses the winner: the order is the contract, not
    // an incidental property of the sort.
    let reversed = Budgets::new(vec![second, first]);
    assert_eq!(
        reversed
            .in_force("Expenses:Rent", "USD", d(2024, 4, 1))
            .map(|b| b.interval),
        Some(Interval::Year)
    );
}

/// `entries()` yields every declaration in effective-date order, and stays an
/// iterator so the storage can be re-indexed later without a major version.
#[test]
fn entries_are_yielded_in_effective_date_order() {
    let b = Budgets::new(vec![
        budget(d(2024, 6, 1), "Expenses:Food", Interval::Month, 450),
        budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 400),
    ]);
    let dates: Vec<_> = b.entries().map(|e| e.from).collect();
    assert_eq!(dates, vec![d(2024, 1, 1), d(2024, 6, 1)]);
    assert_eq!(b.entries().len(), 2);
}

/// A window running to the end of the representable calendar keeps everything
/// accrued before the final, unmeasurable period.
///
/// The last period of the representable calendar has no representable NEXT
/// start, but it still has a length, so it accrues pro-rata like any other.
///
/// Two earlier spellings were wrong. Propagating `None` discarded the entire
/// total: an all-time window returned nothing for a budget worth millions up to
/// that point, and the caller then blamed `Decimal` overflow. Breaking out of
/// the loop kept those millions but silently dropped the final period, so
/// extending the window over it added exactly zero.
///
/// Asserted as a VALUE. The predecessor of this test asserted only that the two
/// windows agreed, which is precisely what the dropped-period bug produced — it
/// pinned the defect instead of the fix.
#[test]
fn the_final_calendar_period_accrues_pro_rata_like_any_other() {
    let b = Budgets::new(vec![budget(
        d(2024, 1, 1),
        "Expenses:Food",
        Interval::Year,
        1200,
    )]);
    let to_last_boundary = b
        .accrue("Expenses:Food", "USD", d(2024, 1, 1), d(9999, 1, 1))
        .expect("a representable total");
    let past_it = b
        .accrue("Expenses:Food", "USD", d(2024, 1, 1), d(9999, 12, 31))
        .expect("extending the window must not discard the total");
    assert!(to_last_boundary > Decimal::from(9_000_000));

    // 9999 is not a leap year, and the window stops one day short of its end.
    let final_stub = Decimal::from(1200) * Decimal::from(364) / Decimal::from(365);
    // Compared with a tolerance: differencing two ~9.5-million totals spends
    // most of `Decimal`'s significant digits, so the last few of the quotient
    // are not recoverable this way. The exact value is asserted below, on a
    // window small enough to carry it.
    let contributed = past_it - to_last_boundary;
    assert!(
        (contributed - final_stub).abs() < Decimal::new(1, 6),
        "the final period must contribute its pro-rata share ({final_stub}), \
         not zero — got {contributed}"
    );

    // A window lying ENTIRELY inside that period is the case the dropped period
    // made indistinguishable from "nothing was budgeted".
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(9999, 1, 1), d(9999, 12, 31)),
        Some(final_stub)
    );
}

/// A period's length is defined at the end of the calendar, where its next
/// start is not. Fixed-length periods keep their length; calendar-aligned ones
/// run to the last representable day.
#[test]
fn the_final_period_still_has_a_length() {
    use rustledger_core::CalendarPeriod;
    assert_eq!(CalendarPeriod::Month.period_days(d(9999, 12, 1)), 31);
    assert_eq!(CalendarPeriod::Quarter.period_days(d(9999, 10, 1)), 92);
    assert_eq!(CalendarPeriod::Year.period_days(d(9999, 1, 1)), 365);
    assert_eq!(CalendarPeriod::Day.period_days(d(9999, 12, 31)), 1);
    assert_eq!(CalendarPeriod::Week.period_days(d(9999, 12, 27)), 7);
    // Away from the edge it must agree with the gap to the next start, which is
    // the definition it replaces.
    for (p, start) in [
        (CalendarPeriod::Month, d(2024, 2, 1)),
        (CalendarPeriod::Quarter, d(2024, 1, 1)),
        (CalendarPeriod::Year, d(2024, 1, 1)),
    ] {
        let next = p.next_start(start).expect("representable");
        let gap = i64::from(
            start
                .until((jiff::Unit::Day, next))
                .map_or(0, |s| s.get_days()),
        );
        assert_eq!(p.period_days(start), gap, "{p:?} at {start}");
    }
}

// ---------------------------------------------------------------------------
// Contract tests for the query surface and the directive reader.
//
// Written from a mutation-testing audit (`cargo mutants -p rustledger-budget`),
// which found 47 of 90 mutants surviving: `parse_budgets` could return nothing,
// every query method could return empty, and every `<` in a date comparison
// could become `<=`, `==` or `>`, with no test noticing. That last group is the
// exact defect class this feature kept shipping — a boundary decided one case
// too wide or too narrow — so these tests assert ON the boundaries rather than
// safely inside them.
// ---------------------------------------------------------------------------

use rust_decimal::Decimal as Dec;
use rustledger_core::{Amount, Custom, Directive, MetaValue};

fn custom(day: NaiveDate, values: Vec<MetaValue>) -> Directive {
    let mut c = Custom::new(day, "budget");
    c.values = values;
    Directive::Custom(c)
}

fn budget_directive(
    day: NaiveDate,
    account: &str,
    interval: &str,
    amount: &str,
    ccy: &str,
) -> Directive {
    custom(
        day,
        vec![
            MetaValue::Account(account.into()),
            MetaValue::String(interval.to_string()),
            MetaValue::Amount(Amount::new(amount.parse::<Dec>().unwrap(), ccy.to_string())),
        ],
    )
}

#[test]
fn parse_budgets_reads_a_well_formed_directive() {
    let dirs = vec![budget_directive(
        d(2024, 1, 1),
        "Expenses:Food",
        "monthly",
        "400.00",
        "USD",
    )];
    let (entries, errors) = parse_budgets(&dirs);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].account, "Expenses:Food");
    assert_eq!(entries[0].currency, "USD");
    assert_eq!(entries[0].interval, Interval::Month);
    assert_eq!(entries[0].amount, Dec::from(400));
    assert_eq!(entries[0].from, d(2024, 1, 1));
}

#[test]
fn parse_budgets_rejects_and_explains_bad_shapes() {
    // Wrong arity, wrong types, an unknown interval, and a second numeric value
    // (a user writing two budgets on one line) must each be reported to the
    // REPORT's caller, not silently dropped or half-read. `rledger check` is
    // stricter and reports only the confident classes — see `BudgetRead`.
    //
    // A directive with no values at all names no account, so it is not ours to
    // judge and produces nothing here.
    let cases: Vec<(Directive, &str)> = vec![
        (
            budget_directive(d(2024, 1, 1), "Expenses:Food", "fortnightly", "1", "USD"),
            "invalid interval",
        ),
        (
            custom(
                d(2024, 1, 1),
                vec![
                    MetaValue::Account("Expenses:Food".into()),
                    MetaValue::String("monthly".to_string()),
                    MetaValue::Amount(Amount::new(Dec::from(400), "USD".to_string())),
                    MetaValue::Number(Dec::from(300)),
                ],
            ),
            "carries a second figure",
        ),
    ];
    for (dir, expect) in cases {
        let (entries, errors) = parse_budgets(&[dir]);
        // A second figure is the ONE bad shape that still yields a budget: Fava
        // reads the first three values and ignores the rest, so discarding the
        // directive would cost the user a budget Fava renders — and, because
        // the report shows only budgeted accounts, the account's whole row.
        let keeps_the_budget = expect.contains("second figure");
        assert_eq!(
            entries.is_empty(),
            !keeps_the_budget,
            "for {expect:?}: {entries:?}"
        );
        assert_eq!(errors.len(), 1, "for {expect:?}");
        assert!(
            errors[0].reason.contains(expect),
            "expected {expect:?} in {:?}",
            errors[0].reason
        );
    }

    // Too weak to claim: no interval keyword, and no account-plus-amount pair.
    // Ownership of the `custom "budget"` name is one rule, tabulated in the
    // CLI's `ownership_of_the_custom_budget_namespace`.
    for weak in [vec![], vec![MetaValue::Account("Expenses:Food".into())]] {
        let (entries, errors) = parse_budgets(&[custom(d(2024, 1, 1), weak.clone())]);
        assert!(
            entries.is_empty() && errors.is_empty(),
            "{weak:?} is not ours: {errors:?}"
        );
    }

    // An account AND an amount IS ours, even with the interval word forgotten:
    // two values leave no room for another tool's schema, and reporting nothing
    // meant the report claimed "No budgets declared" over a ledger that plainly
    // declared one.
    let (entries, errors) = parse_budgets(&[custom(
        d(2024, 1, 1),
        vec![
            MetaValue::Account("Expenses:Food".into()),
            MetaValue::Amount(Amount::new(Dec::from(400), "USD".to_string())),
        ],
    )]);
    assert!(entries.is_empty(), "no interval, so no budget: {entries:?}");
    assert_eq!(errors.len(), 1, "...but it is reported: {errors:?}");
}

#[test]
fn parse_budgets_accepts_a_quoted_account_and_a_trailing_note() {
    let dirs = vec![custom(
        d(2024, 1, 1),
        vec![
            MetaValue::String("Expenses:Food".to_string()),
            MetaValue::String("monthly".to_string()),
            MetaValue::Amount(Amount::new(Dec::from(400), "USD".to_string())),
            MetaValue::String("groceries only".to_string()),
        ],
    )];
    let (entries, errors) = parse_budgets(&dirs);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].account, "Expenses:Food");
}

/// A first value that is not an account name, in a directive that OTHERWISE has
/// Fava's shape, is a budget with a broken account — reported, and never read as
/// an account. A name carrying a newline would otherwise forge a row in the
/// fixed-width text table.
///
/// The shape is what decides. A payload whose second value is not a quoted
/// interval is another tool's and stays silent — that is
/// `check_does_not_claim_another_tools_custom_budget`, over in the CLI tests.
#[test]
fn a_quoted_string_that_is_not_an_account_is_reported_never_read() {
    for bad in ["not an account", "Expenses", "", "Expenses:Food\nTOTAL 9"] {
        let dirs = vec![custom(
            d(2024, 1, 1),
            vec![
                MetaValue::String(bad.to_string()),
                MetaValue::String("monthly".to_string()),
                MetaValue::Amount(Amount::new(Dec::from(400), "USD".to_string())),
            ],
        )];
        let (entries, errors) = parse_budgets(&dirs);
        assert!(entries.is_empty(), "{bad:?} must not parse as an account");
        assert_eq!(errors.len(), 1, "{bad:?} has Fava's shape, so say so");
        assert!(
            errors[0].reason.contains("not a valid account name"),
            "{bad:?}: {:?}",
            errors[0].reason
        );
    }
}

#[test]
fn parse_budgets_ignores_other_custom_types() {
    let mut c = Custom::new(d(2024, 1, 1), "not-a-budget");
    c.values = vec![MetaValue::Account("Expenses:Food".into())];
    let (entries, errors) = parse_budgets(&[Directive::Custom(c)]);
    assert!(entries.is_empty() && errors.is_empty());
}

/// `before` is EXCLUSIVE. A budget declared exactly on it is not yet in force;
/// one declared the day before is. Both mutants `<= ` and `>` flip exactly one
/// of these.
#[test]
fn in_force_before_is_exclusive_at_the_boundary() {
    let b = Budgets::new(vec![budget(
        d(2024, 6, 15),
        "Expenses:Food",
        Interval::Month,
        400,
    )]);
    // `any_in_force_before` used to be asserted here too. It had no caller
    // outside this test, so it was removed rather than published — the bound it
    // encoded is the same one `keys_in_force_before` answers, and that one is
    // load-bearing.
    assert!(b.keys_in_force_before(d(2024, 6, 15)).is_empty());
    assert_eq!(
        b.keys_in_force_before(d(2024, 6, 16)),
        vec![(Account::new("Expenses:Food"), Currency::new("USD"))]
    );
}

/// `in_force` is INCLUSIVE of the declaration day, unlike `*_before`. The pair
/// of boundaries is easy to write one apart; assert both.
#[test]
fn in_force_includes_the_declaration_day() {
    let b = Budgets::new(vec![budget(
        d(2024, 6, 15),
        "Expenses:Food",
        Interval::Month,
        400,
    )]);
    assert!(b.in_force("Expenses:Food", "USD", d(2024, 6, 14)).is_none());
    assert!(b.in_force("Expenses:Food", "USD", d(2024, 6, 15)).is_some());
    // Keyed on the PAIR: neither a different account nor a different currency
    // may resolve to it.
    assert!(b.in_force("Expenses:Foo", "USD", d(2024, 6, 15)).is_none());
    assert!(b.in_force("Expenses:Food", "EUR", d(2024, 6, 15)).is_none());
}

#[test]
fn effective_start_is_the_earliest_for_the_pair_only() {
    let b = Budgets::new(vec![
        budget(d(2024, 6, 1), "Expenses:Food", Interval::Month, 450),
        budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 400),
        budget(d(2023, 1, 1), "Expenses:Rent", Interval::Month, 900),
    ]);
    assert_eq!(
        b.effective_start("Expenses:Food", "USD"),
        Some(d(2024, 1, 1))
    );
    assert_eq!(
        b.effective_start("Expenses:Rent", "USD"),
        Some(d(2023, 1, 1))
    );
    assert_eq!(b.effective_start("Expenses:Food", "EUR"), None);
    assert_eq!(b.effective_start("Expenses:Nope", "USD"), None);
}

/// `next_change_after` is STRICTLY after: a declaration on the same day is not
/// a future change, or the accrual would split a segment at a boundary it has
/// already passed.
#[test]
fn next_change_after_is_strict() {
    let b = Budgets::new(vec![
        budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 400),
        budget(d(2024, 6, 1), "Expenses:Food", Interval::Month, 450),
    ]);
    assert_eq!(
        b.next_change_after("Expenses:Food", "USD", d(2024, 1, 1)),
        Some(d(2024, 6, 1))
    );
    assert_eq!(
        b.next_change_after("Expenses:Food", "USD", d(2024, 6, 1)),
        None,
        "the same day is not a later change"
    );
    assert_eq!(
        b.next_change_after("Expenses:Food", "EUR", d(2024, 1, 1)),
        None
    );
}

#[test]
fn all_keys_is_every_declared_pair_regardless_of_date() {
    let b = Budgets::new(vec![
        budget(d(2099, 1, 1), "Expenses:Food", Interval::Month, 400),
        budget(d(2024, 1, 1), "Expenses:Rent", Interval::Month, 900),
        budget(d(2024, 2, 1), "Expenses:Rent", Interval::Month, 950),
    ]);
    assert_eq!(
        b.all_keys(),
        vec![
            (Account::new("Expenses:Food"), Currency::new("USD")),
            (Account::new("Expenses:Rent"), Currency::new("USD")),
        ],
        "deduplicated, and a future declaration still counts"
    );
    // ...while the windowed view excludes the future one.
    assert_eq!(b.keys_in_force_before(d(2024, 6, 1)).len(), 1);
}

#[test]
fn is_empty_and_earliest_reflect_the_entries() {
    let none = Budgets::default();
    assert!(none.is_empty());
    assert_eq!(none.earliest(), None);
    assert_eq!(none.entries().len(), 0);

    let some = Budgets::new(vec![
        budget(d(2024, 6, 1), "Expenses:Food", Interval::Month, 450),
        budget(d(2023, 3, 1), "Expenses:Rent", Interval::Month, 900),
    ]);
    assert!(!some.is_empty());
    assert_eq!(some.earliest(), Some(d(2023, 3, 1)));
}

/// `accrue` over an empty or inverted window is zero, not a panic and not a
/// whole period. `from == to` is the case a caller hits by asking for one day.
#[test]
fn accrue_over_an_empty_window_is_zero() {
    let b = Budgets::new(vec![budget(
        d(2024, 1, 1),
        "Expenses:Food",
        Interval::Month,
        400,
    )]);
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 3, 5), d(2024, 3, 5)),
        Some(Decimal::ZERO)
    );
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 3, 6), d(2024, 3, 5)),
        Some(Decimal::ZERO)
    );
    // An unbudgeted pair accrues nothing rather than erroring.
    assert_eq!(
        b.accrue("Expenses:Food", "EUR", d(2024, 1, 1), d(2024, 2, 1)),
        Some(Decimal::ZERO)
    );
}

/// `from_directives` must actually read the ledger, not just hand back an empty
/// index. Mutating it to `(Default::default(), vec![])` survived every other
/// test because they all build `Budgets` by hand.
#[test]
fn from_directives_indexes_what_it_parsed() {
    let dirs = vec![
        budget_directive(d(2024, 1, 1), "Expenses:Food", "monthly", "400.00", "USD"),
        budget_directive(d(2024, 6, 1), "Expenses:Food", "monthly", "450.00", "USD"),
        budget_directive(
            d(2024, 1, 1),
            "Expenses:Rent",
            "fortnightly",
            "900.00",
            "USD",
        ),
    ];
    let budgets = Budgets::from_directives(&dirs);
    let errors = budgets.errors().to_vec();
    assert_eq!(errors.len(), 1, "the bad interval is reported");
    assert!(!budgets.is_empty());
    assert_eq!(budgets.entries().len(), 2);
    assert_eq!(budgets.earliest(), Some(d(2024, 1, 1)));
    // A whole month at each rate, proving the entries are usable and ordered.
    assert_eq!(
        budgets.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2024, 2, 1)),
        Some(Decimal::from(400))
    );
    assert_eq!(
        budgets.accrue("Expenses:Food", "USD", d(2024, 6, 1), d(2024, 7, 1)),
        Some(Decimal::from(450))
    );
}

/// The "no budget yet in force" branch skips the cursor to the next declaration
/// only when that declaration is INSIDE the window; otherwise it stops. Both
/// halves matter: `next < to` relaxed to `<=` or to `true` would step to a
/// declaration on or past the end and accrue a period that is not in range.
#[test]
fn accrue_skips_to_a_later_declaration_only_inside_the_window() {
    let b = Budgets::new(vec![budget(
        d(2024, 6, 15),
        "Expenses:Food",
        Interval::Day,
        10,
    )]);
    // Window ends exactly ON the declaration: nothing is in force in it.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2024, 6, 15)),
        Some(Decimal::ZERO),
        "a declaration on the exclusive end is outside the window"
    );
    // Window ends one day later: exactly one day accrues.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2024, 6, 16)),
        Some(Decimal::from(10))
    );
}

/// A superseding declaration splits the segment only when it lands strictly
/// INSIDE it. Landing exactly on the segment end changes nothing, and relaxing
/// that to `<=` re-splits a boundary already accounted for.
#[test]
fn a_supersession_on_the_segment_boundary_does_not_resplit_it() {
    // The second declaration falls exactly on the month boundary, which is
    // already where the segment ends.
    let b = Budgets::new(vec![
        budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 310),
        budget(d(2024, 2, 1), "Expenses:Food", Interval::Month, 290),
    ]);
    // January in full at 310, February in full at 290.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2024, 3, 1)),
        Some(Decimal::from(600))
    );
    // And a mid-month supersession still splits: 14 days of Feb at 290/29 plus
    // 15 at 580/29.
    let mid = Budgets::new(vec![
        budget(d(2024, 2, 1), "Expenses:Food", Interval::Month, 290),
        budget(d(2024, 2, 15), "Expenses:Food", Interval::Month, 580),
    ]);
    let want = Decimal::from(290) * Decimal::from(14) / Decimal::from(29)
        + Decimal::from(580) * Decimal::from(15) / Decimal::from(29);
    assert_eq!(
        mid.accrue("Expenses:Food", "USD", d(2024, 2, 1), d(2024, 3, 1)),
        Some(want)
    );
}

/// A zero-length segment contributes nothing. `seg_days > 0` relaxed to `>= 0`
/// would divide a zero-day segment into the total, which is only harmless by
/// accident.
#[test]
fn a_zero_day_segment_contributes_nothing() {
    let b = Budgets::new(vec![budget(
        d(2024, 1, 1),
        "Expenses:Food",
        Interval::Month,
        400,
    )]);
    // One single day, at the very start of a month: exactly 400/31.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2024, 1, 2)),
        Some(Decimal::from(400) / Decimal::from(31))
    );
    // And the degenerate window contributes nothing at all.
    assert_eq!(
        b.accrue("Expenses:Food", "USD", d(2024, 1, 1), d(2024, 1, 1)),
        Some(Decimal::ZERO)
    );
}

/// A sibling whose name sorts BETWEEN a parent and its children must not hide
/// them.
///
/// The subtree lookups are `BTreeMap`/`BTreeSet` ranges, and account names sort
/// bytewise: `'0'` is 0x30 and `':'` is 0x3A, so `Expenses:Food0` falls between
/// `Expenses:Food` and `Expenses:Food:Restaurant`. A range that stopped at the
/// first non-covered account would drop the child sitting behind the sibling —
/// the row would report the parent's own budget and none of its subtree's, with
/// nothing to indicate the omission.
#[test]
fn a_sibling_sorting_inside_the_subtree_does_not_truncate_it() {
    use rustledger_core::AccountTypes;
    let b = Budgets::new(vec![
        budget(d(2024, 1, 1), "Expenses:Food", Interval::Month, 100),
        // Sorts between the two above. Valid beancount: components may carry
        // digits and dashes after the first character.
        budget(d(2024, 1, 1), "Expenses:Food0", Interval::Month, 7),
        budget(d(2024, 1, 1), "Expenses:Food-Bar", Interval::Month, 9),
        budget(
            d(2024, 1, 1),
            "Expenses:Food:Restaurant",
            Interval::Month,
            400,
        ),
    ]);
    let cmp = b.compare(
        &[],
        &AccountTypes::default(),
        d(2024, 2, 1),
        d(2024, 3, 1),
        true,
        None,
    );
    let food = cmp
        .rows
        .iter()
        .find(|r| r.account == "Expenses:Food")
        .expect("the parent row must exist");
    assert_eq!(
        food.budgeted,
        Some(Decimal::from(500)),
        "the parent aggregates its own 100 and the child's 400 — the siblings \
         that sort between them are not part of the subtree and must neither \
         be counted nor hide the child"
    );
    // ...and the siblings are their own rows, at their own amounts.
    for (account, want) in [("Expenses:Food0", 7), ("Expenses:Food-Bar", 9)] {
        let row = cmp
            .rows
            .iter()
            .find(|r| r.account == account)
            .unwrap_or_else(|| panic!("no row for {account}"));
        assert_eq!(row.budgeted, Some(Decimal::from(want)), "{account}");
    }
}

/// The indexed supersession lookups must answer exactly what the linear scans
/// they replaced answered, including the cases that make the index subtle:
/// several declarations on ONE date (supersession takes the last in caller
/// order), two currencies for one account (parallel, neither superseding), and
/// a key with no declarations at all.
///
/// Differential rather than by-example: `in_force` is now a `partition_point`
/// over per-key positions, and the property that matters is agreement with the
/// definition, not any particular answer.
#[test]
fn the_indexed_lookups_agree_with_a_linear_scan() {
    let mut entries = Vec::new();
    for (day, account, amount) in [
        (1, "Expenses:Food", 100),
        (1, "Expenses:Food", 200), // same date — the LAST one wins
        (1, "Expenses:Food", 300),
        (5, "Expenses:Food", 400),
        (5, "Expenses:Rent", 950),
        (9, "Expenses:Food", 500),
        (3, "Expenses:Rent", 900),
    ] {
        entries.push(budget(d(2024, 6, day), account, Interval::Month, amount));
    }
    // A second currency for an account that already has one: parallel budgets.
    let mut eur = budget(d(2024, 6, 4), "Expenses:Food", Interval::Month, 77);
    eur.currency = Currency::new("EUR");
    entries.push(eur);

    let b = Budgets::new(entries.clone());
    // The definition, as the code read before the index: entries are sorted by
    // `from`, and the entry in force is the LAST one dated on or before the day.
    let mut sorted = entries.clone();
    sorted.sort_by_key(|e| e.from);

    for account in ["Expenses:Food", "Expenses:Rent", "Expenses:Nothing"] {
        for currency in ["USD", "EUR", "GBP"] {
            for day in 1..=12 {
                let day = d(2024, 6, day);

                let want = sorted
                    .iter()
                    .rfind(|e| e.account == account && e.currency == currency && e.from <= day);
                assert_eq!(
                    b.in_force(account, currency, day).map(|e| e.amount),
                    want.map(|e| e.amount),
                    "in_force({account}, {currency}, {day})"
                );

                let want_next = sorted
                    .iter()
                    .filter(|e| e.account == account && e.currency == currency && e.from > day)
                    .map(|e| e.from)
                    .min();
                assert_eq!(
                    b.next_change_after(account, currency, day),
                    want_next,
                    "next_change_after({account}, {currency}, {day})"
                );
            }

            let want_start = sorted
                .iter()
                .filter(|e| e.account == account && e.currency == currency)
                .map(|e| e.from)
                .min();
            assert_eq!(
                b.effective_start(account, currency),
                want_start,
                "effective_start({account}, {currency})"
            );
        }
    }

    // The same-date case, spelled out: the last declaration on 2024-06-01 is the
    // one in force that day, not the first and not an arbitrary one.
    assert_eq!(
        b.in_force("Expenses:Food", "USD", d(2024, 6, 1))
            .map(|e| e.amount),
        Some(Decimal::from(300))
    );
}

/// The `Empty` diagnosis, at the level that owns it.
///
/// Three different answers — "you have no budgets", "yours start later than
/// this window", "your filter excluded them all" — and telling a user with
/// budgets that they have none sends them looking for a parsing bug that is not
/// there. The `code` is what a dashboard branches on, so each must differ.
#[test]
fn an_empty_report_says_which_kind_of_empty() {
    use rustledger_core::AccountTypes;
    let types = AccountTypes::default();
    let window = |b: &Budgets, filter: Option<&str>, to: NaiveDate| {
        b.compare(&[], &types, d(2024, 1, 1), to, false, filter)
            .empty
    };

    // Nothing declared at all.
    let none = Budgets::new(vec![]);
    assert_eq!(
        window(&none, None, d(2024, 2, 1)),
        Some(Empty::NoneDeclared)
    );

    // Declared, but every one starts on or after the exclusive end. The bound
    // is what `<` vs `<=` turns on: a budget dated ON `to` is not in force.
    let later = Budgets::new(vec![budget(
        d(2024, 6, 1),
        "Expenses:Food",
        Interval::Month,
        400,
    )]);
    assert_eq!(
        window(&later, None, d(2024, 6, 1)),
        Some(Empty::NoneInWindow {
            earliest: d(2024, 6, 1)
        }),
        "a budget starting exactly on the exclusive end is not in force"
    );
    // One day past it, the budget IS in force, so the report is not empty.
    assert_eq!(window(&later, None, d(2024, 6, 2)), None);

    // In force, but the filter excluded them.
    assert_eq!(
        window(&later, Some("Income"), d(2024, 7, 1)),
        Some(Empty::FilteredOut)
    );

    // Every code is distinct — they are the machine-readable half.
    let codes = [
        Empty::NoneDeclared.code(),
        Empty::AllRejected { shown: true }.code(),
        Empty::NoneInWindow {
            earliest: d(2024, 1, 1),
        }
        .code(),
        Empty::FilteredOut.code(),
    ];
    let unique: std::collections::BTreeSet<_> = codes.iter().collect();
    assert_eq!(unique.len(), codes.len(), "{codes:?}");
    assert_eq!(codes[0], "none_declared");
    assert_eq!(codes[1], "all_rejected");
    assert_eq!(codes[2], "none_in_window");
    assert_eq!(codes[3], "filtered_out");
}

/// A directive that names something unusable quotes it back, so the user can
/// find the line. The value is rendered, not `Debug`-formatted: a diagnostic
/// reading `String("Expenses:food")` leaks Rust type names at a user.
#[test]
fn an_unusable_account_is_quoted_back_readably() {
    use rustledger_core::{Amount, Custom, MetaValue};
    let mut c = Custom::new(d(2024, 1, 1), "budget");
    c.values = vec![
        MetaValue::String("Expenses:food".to_string()),
        MetaValue::String("monthly".to_string()),
        MetaValue::Amount(Amount::new(Decimal::from(400), "USD")),
    ];
    let BudgetRead::Invalid(e) = read_budget(&c) else {
        panic!("a Fava-shaped directive with a bad account is ours to report");
    };
    assert!(
        e.reason.contains(r#""Expenses:food""#),
        "the offending text must appear verbatim: {}",
        e.reason
    );
    assert!(
        !e.reason.contains("String("),
        "rendered, not Debug-formatted: {}",
        e.reason
    );
}

/// `AllRejected { shown }` distinguishes "each rejection is on screen" from
/// "your filter removed them" — the two get different advice, and the second
/// must not tell the user to look at warnings that are not there.
#[test]
fn all_rejected_says_whether_the_warnings_survived_the_filter() {
    use rustledger_core::{AccountTypes, Amount, Custom, MetaValue};
    let types = AccountTypes::default();
    let bad = |account: &str| {
        let mut c = Custom::new(d(2024, 1, 1), "budget");
        c.values = vec![
            MetaValue::Account(Account::new(account)),
            MetaValue::String("fortnightly".to_string()),
            MetaValue::Amount(Amount::new(Decimal::from(400), "USD")),
        ];
        Directive::Custom(c)
    };
    let dirs = vec![bad("Expenses:Food")];
    let b = Budgets::new(vec![]);
    assert!(b.is_empty(), "the fixture must parse no usable budget");

    let b = Budgets::from_directives(&dirs);
    assert!(b.is_empty() && !b.errors().is_empty());

    // Unfiltered: the rejection is on screen.
    let seen = b.compare(&dirs, &types, d(2024, 1, 1), d(2024, 2, 1), false, None);
    assert_eq!(seen.empty, Some(Empty::AllRejected { shown: true }));
    assert_eq!(seen.errors.len(), 1);

    // Filtered away: still all-rejected, but do not point at absent warnings.
    let hidden = b.compare(
        &dirs,
        &types,
        d(2024, 1, 1),
        d(2024, 2, 1),
        false,
        Some("Income"),
    );
    assert_eq!(hidden.empty, Some(Empty::AllRejected { shown: false }));
    assert!(hidden.errors.is_empty());
}
