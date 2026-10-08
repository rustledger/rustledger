//! The order `extract` writes a statement's directives in (#2319).
//!
//! Banks export in either direction: oldest-first, or newest-first like many
//! web banking downloads. A ledger reads oldest-first, and the user asked
//! that the export's *sequence* survive, so neither "keep file order" nor a
//! plain sort by date is right:
//!
//! - keeping file order writes a newest-first export backwards;
//! - a plain stable sort by date (what beangulp does) fixes the days but
//!   leaves each day's rows newest-first, the order the bank listed them.
//!
//! [`chronological`] works out which way the export runs, turns a
//! newest-first one round, and only then sorts by date. That gives
//! chronological order across days *and* within a day.
//!
//! The assumption it rests on: an export that runs newest-first across days
//! also runs newest-first within a day. Neither CSV nor OFX gives a time of
//! day that could check it, so a bank that sorts days descending but lists
//! each day's rows oldest-first comes out with those days' rows reversed.

use rustledger_core::{Directive, booking_sort_key};

/// Put one statement's directives in ledger order: oldest first, keeping
/// the export's sequence within each day.
///
/// 1. Count the steps between consecutive transactions' dates, in file
///    order: up (a later date follows) or down (an earlier one does).
///    Same-date neighbors say nothing about direction and are not counted.
/// 2. More steps down than up means a newest-first export: reverse it.
/// 3. Stable-sort by [`booking_sort_key`], the canonical directive order
///    (date, then directive type). Directives on the same date and of the
///    same type keep their (post-reversal) position.
///
/// Only transactions vote in step 1: they are the statement's rows. A
/// directive an importer adds from elsewhere in the file, such as the
/// balance assertion an OFX `LEDGERBAL` becomes, is not a row and is placed
/// by the sort alone.
///
/// Moving a balance assertion cannot change whether it holds. Beancount and
/// `rledger check` both evaluate a `balance` at the START of its date, before
/// that day's transactions, whatever line it is written on: the loader sorts
/// by (date, directive type) and a balance ranks ahead of a transaction. The
/// sort here uses that same key, so an assertion dated on a statement's last
/// day is written ahead of that day's rows, which is where it is checked. (A
/// closing balance must be dated the day after; the OFX importer does that.)
///
/// A tie, including a statement whose rows all share one date, keeps file
/// order: the direction cannot be told, and guessing would reorder a day.
/// An oldest-first statement comes back exactly as it went in.
///
/// Call once per input file. Two files are two statements, each with its own
/// direction, so their directives are ordered separately and kept as
/// separate blocks rather than merged.
#[must_use]
pub fn chronological(mut directives: Vec<Directive>) -> Vec<Directive> {
    if runs_newest_first(&directives) {
        directives.reverse();
    }
    // `sort_by_key` is stable, which is what keeps the within-day sequence.
    directives.sort_by_key(booking_sort_key);
    directives
}

/// Whether the statement's dates step down more often than up.
fn runs_newest_first(directives: &[Directive]) -> bool {
    let (mut up, mut down) = (0usize, 0usize);
    let mut dates = directives.iter().filter_map(|d| match d {
        Directive::Transaction(txn) => Some(txn.date),
        _ => None,
    });
    let Some(mut previous) = dates.next() else {
        return false;
    };
    for date in dates {
        match date.cmp(&previous) {
            std::cmp::Ordering::Greater => up += 1,
            std::cmp::Ordering::Less => down += 1,
            std::cmp::Ordering::Equal => {}
        }
        previous = date;
    }
    down > up
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::csv_importer::CsvImporter;
    use crate::{ImporterConfig, ofx_importer::OfxImporter};
    use proptest::prelude::*;
    use rustledger_core::NaiveDate;

    fn config() -> ImporterConfig {
        ImporterConfig::csv()
            .account("Assets:Bank")
            .currency("USD")
            .date_column("Date")
            .narration_column("Description")
            .amount_column("Amount")
            .build()
            .unwrap()
    }

    /// The statement's rows, as `(date, narration)`, in output order.
    fn extract(rows: &[(String, String)]) -> Vec<(NaiveDate, String)> {
        let mut csv = String::from("Date,Description,Amount\n");
        for (date, narration) in rows {
            csv.push_str(&format!("{date},{narration},-1.00\n"));
        }
        let result = CsvImporter.extract_string(&csv, &config()).unwrap();
        assert!(result.warnings.is_empty(), "{:?}", result.warnings);
        chronological(result.directives)
            .into_iter()
            .map(|d| match d {
                Directive::Transaction(t) => (t.date, t.narration.to_string()),
                other => panic!("only transactions expected, got {other:?}"),
            })
            .collect()
    }

    fn rows(spec: &[(&str, &str)]) -> Vec<(String, String)> {
        spec.iter()
            .map(|(d, n)| ((*d).to_string(), (*n).to_string()))
            .collect()
    }

    fn narrations(out: &[(NaiveDate, String)]) -> Vec<&str> {
        out.iter().map(|(_, n)| n.as_str()).collect()
    }

    /// A non-decreasing run of dates over at least two distinct days, with a
    /// unique narration per row so any reordering is visible.
    fn monotonic_statement() -> impl Strategy<Value = Vec<(String, String)>> {
        prop::collection::vec(0u8..3, 1..25).prop_map(|steps| {
            // Day 1, then each step adds 0..=2 days; a forced final step of
            // one day guarantees two distinct dates.
            // Day n is in month n / 28 + 1, so every day number is a date.
            let date = |n: u32| format!("2024-{:02}-{:02}", n / 28 + 1, n % 28 + 1);
            let mut day = 0u32;
            let mut out = vec![(date(day), "r0".to_string())];
            for (i, step) in steps.iter().enumerate() {
                day += u32::from(*step);
                out.push((date(day), format!("r{}", i + 1)));
            }
            day += 1;
            out.push((date(day), format!("r{}", steps.len() + 1)));
            out
        })
    }

    proptest! {
        /// #2319: for any statement whose dates only go one way, which way
        /// the bank wrote it does not change the output: extract(F) ==
        /// extract(reverse(F)), and both are F, the oldest-first order.
        #[test]
        fn direction_of_a_monotonic_statement_does_not_matter(f in monotonic_statement()) {
            let mut reversed = f.clone();
            reversed.reverse();
            let forward = extract(&f);
            prop_assert_eq!(&forward, &extract(&reversed));
            let expected: Vec<&str> = f.iter().map(|(_, n)| n.as_str()).collect();
            prop_assert_eq!(narrations(&forward), expected);
        }
    }

    proptest! {
        /// An oldest-first statement's directives come back unchanged, as
        /// values and not just in order: its output is byte-identical to
        /// what `extract` wrote before ordering existed.
        #[test]
        fn an_ascending_statement_is_returned_as_is(f in monotonic_statement()) {
            let mut csv = String::from("Date,Description,Amount\n");
            for (date, narration) in &f {
                csv.push_str(&format!("{date},{narration},-1.00\n"));
            }
            let imported = CsvImporter.extract_string(&csv, &config()).unwrap().directives;
            prop_assert_eq!(chronological(imported.clone()), imported);
        }
    }

    /// An oldest-first statement comes back exactly as it went in, same-day
    /// rows included.
    #[test]
    fn an_ascending_statement_is_unchanged() {
        let f = rows(&[
            ("2024-01-01", "a"),
            ("2024-01-01", "b"),
            ("2024-01-02", "c"),
            ("2024-01-05", "d"),
            ("2024-01-05", "e"),
        ]);
        assert_eq!(narrations(&extract(&f)), ["a", "b", "c", "d", "e"]);
    }

    /// A newest-first statement is turned round within the day too: the
    /// bank's last-listed row of a day is that day's first.
    #[test]
    fn a_descending_statement_is_reversed_within_each_day() {
        let f = rows(&[
            ("2024-01-03", "late-2"),
            ("2024-01-03", "late-1"),
            ("2024-01-02", "mid"),
            ("2024-01-01", "early-2"),
            ("2024-01-01", "early-1"),
        ]);
        assert_eq!(
            narrations(&extract(&f)),
            ["early-1", "early-2", "mid", "late-1", "late-2"]
        );
    }

    /// Mostly ascending with rows out of place (or grouped by something
    /// other than date): sorted by date, with each day's rows in file order.
    #[test]
    fn an_unsorted_statement_is_sorted_keeping_file_order_within_a_day() {
        let f = rows(&[
            ("2024-01-02", "b1"),
            ("2024-01-01", "a1"),
            ("2024-01-03", "c1"),
            ("2024-01-04", "d1"),
            ("2024-01-02", "b2"),
            ("2024-01-05", "e1"),
            ("2024-01-01", "a2"),
            ("2024-01-06", "f1"),
        ]);
        assert_eq!(
            narrations(&extract(&f)),
            ["a1", "a2", "b1", "b2", "c1", "d1", "e1", "f1"]
        );
    }

    /// Grouped by payee, each group ascending: as many steps down as the
    /// groups have boundaries, fewer than the steps up, so no reversal.
    #[test]
    fn a_grouped_statement_is_date_sorted() {
        let f = rows(&[
            ("2024-01-01", "shop-1"),
            ("2024-01-03", "shop-3"),
            ("2024-01-05", "shop-5"),
            ("2024-01-02", "cafe-2"),
            ("2024-01-04", "cafe-4"),
            ("2024-01-06", "cafe-6"),
        ]);
        assert_eq!(
            narrations(&extract(&f)),
            ["shop-1", "cafe-2", "shop-3", "cafe-4", "shop-5", "cafe-6"]
        );
    }

    /// One date throughout: no direction to read, so file order is kept.
    #[test]
    fn a_single_date_statement_keeps_file_order() {
        let f = rows(&[
            ("2024-01-01", "x"),
            ("2024-01-01", "y"),
            ("2024-01-01", "z"),
        ]);
        assert_eq!(narrations(&extract(&f)), ["x", "y", "z"]);
    }

    /// As many steps down as up: a tie is not a newest-first export, so the
    /// rows are only sorted, never reversed.
    #[test]
    fn a_tie_is_not_reversed() {
        // 2 -> 1 is down, 1 -> 1 is not counted, 1 -> 2 is up.
        let f = rows(&[
            ("2024-01-02", "b1"),
            ("2024-01-01", "a1"),
            ("2024-01-01", "a2"),
            ("2024-01-02", "b2"),
        ]);
        assert_eq!(narrations(&extract(&f)), ["a1", "a2", "b1", "b2"]);
    }

    /// A balance an importer emits on the statement's last date is written
    /// ahead of that day's transactions: that is where beancount and
    /// `rledger check` evaluate it whatever its line, so the output reads the
    /// way it is checked and the check result cannot change.
    #[test]
    fn a_same_date_balance_is_written_before_that_days_transactions() {
        use rustledger_core::{Amount, Balance};
        let mut directives = CsvImporter
            .extract_string(
                "Date,Description,Amount\n2024-01-03,c,-1.00\n2024-01-02,b,-1.00\n",
                &config(),
            )
            .unwrap()
            .directives;
        directives.push(Directive::Balance(Balance::new(
            "2024-01-03".parse().unwrap(),
            "Assets:Bank",
            Amount::new(rust_decimal::Decimal::new(100, 0), "USD"),
        )));
        let shape: Vec<String> = chronological(directives)
            .iter()
            .map(|d| match d {
                Directive::Transaction(t) => format!("{} {}", t.date, t.narration),
                Directive::Balance(b) => format!("{} balance", b.date),
                other => format!("{other:?}"),
            })
            .collect();
        assert_eq!(
            shape,
            ["2024-01-02 b", "2024-01-03 balance", "2024-01-03 c"]
        );
    }

    /// The OFX `LEDGERBAL` assertion is not a row: it does not vote on
    /// direction, and the sort places it by date like any directive.
    #[test]
    fn an_ofx_statement_balance_does_not_vote_and_lands_by_date() {
        let ofx = "<OFX><BANKMSGSRSV1><STMTTRNRS><STMTRS><CURDEF>USD\
            <BANKTRANLIST>\
            <STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240103<TRNAMT>-3.00<FITID>3<NAME>Third</STMTTRN>\
            <STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240102<TRNAMT>-2.00<FITID>2<NAME>Second</STMTTRN>\
            <STMTTRN><TRNTYPE>DEBIT<DTPOSTED>20240101<TRNAMT>-1.00<FITID>1<NAME>First</STMTTRN>\
            </BANKTRANLIST>\
            <LEDGERBAL><BALAMT>100.00<DTASOF>20240103</LEDGERBAL>\
            </STMTRS></STMTTRNRS></BANKMSGSRSV1></OFX>";
        let result = OfxImporter.extract_from_string(ofx, &config()).unwrap();
        let out = chronological(result.directives);
        let shape: Vec<String> = out
            .iter()
            .map(|d| match d {
                Directive::Transaction(t) => {
                    format!("{} {}", t.date, t.payee.as_deref().unwrap_or(&t.narration))
                }
                Directive::Balance(b) => format!("{} balance", b.date),
                other => format!("{other:?}"),
            })
            .collect();
        let last = shape.last().unwrap().clone();
        assert!(last.ends_with("balance"), "{shape:?}");
        let txns: Vec<&String> = shape.iter().filter(|s| !s.ends_with("balance")).collect();
        assert_eq!(txns.len(), 3, "{shape:?}");
        assert!(txns[0].starts_with("2024-01-01"), "{shape:?}");
        assert!(txns[2].starts_with("2024-01-03"), "{shape:?}");
    }
}
