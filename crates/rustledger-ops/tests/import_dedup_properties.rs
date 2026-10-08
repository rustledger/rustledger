//! Property tests for `find_import_duplicates` (#2421): the invariants a
//! re-import must keep, over generated statements that include repeated
//! identical rows, empty text, id links, other commodities and rows posting
//! outside the importer's account.

use proptest::prelude::*;
use rust_decimal::Decimal;
use rustledger_core::{Amount, Posting, Transaction};
use rustledger_ops::dedup::{FuzzyDedupConfig, ImportDuplicate, find_import_duplicates};

const BANK: &str = "Assets:Bank";

/// A statement row: (day, cents, currency, on the bank account?, text, has an
/// id?). A row's id is derived from its position in its statement, so ids are
/// unique within one statement, as a bank's are; two statements can still
/// share an id with different content, which is the sanitizer-collision case.
type Row = (u8, i64, &'static str, bool, &'static str, bool);

fn row() -> impl Strategy<Value = Row> {
    (
        0u8..3,
        prop::sample::select(vec![-100i64, -250, -400]),
        prop::sample::select(vec!["EUR", "USD"]),
        prop::bool::weighted(0.9),
        // Includes "" (a CSV with no description) and a pair where one text
        // contains the other ("coffee" and "shop" both inside "coffee shop"),
        // so two different rows can compete for one entry and the fuzzy pass is
        // exercised, not only exact matches.
        prop::sample::select(vec!["coffee", "coffee shop", "shop", "rent", "tea", ""]),
        prop::bool::weighted(0.3),
    )
}

/// Rows that all share one date, amount and account, so they compete for the
/// same entries and only text and ids tell them apart: the shape where the
/// order rows are visited in could matter.
fn crowded_row() -> impl Strategy<Value = Row> {
    (
        Just(0u8),
        Just(-400i64),
        Just("EUR"),
        Just(true),
        prop::sample::select(vec!["coffee", "coffee shop", "shop", "tea", ""]),
        prop::bool::weighted(0.2),
    )
}

fn txn(pos: usize, r: &Row) -> Transaction {
    let (day, cents, ccy, on_bank, text, has_id) = *r;
    let date = format!("2024-01-1{day}").parse().unwrap();
    let account = if on_bank { BANK } else { "Assets:Wallet" };
    let mut t = Transaction::new(date, text)
        .with_synthesized_posting(Posting::new(
            account,
            Amount::new(Decimal::new(cents, 2), ccy),
        ))
        .with_synthesized_posting(Posting::auto("Expenses:Unknown"));
    if has_id {
        t = t.with_link(format!("csv-{pos}"));
    }
    t
}

fn dedup(new: &[Transaction], existing: &[Transaction]) -> Vec<ImportDuplicate> {
    let new: Vec<&Transaction> = new.iter().collect();
    let existing: Vec<&Transaction> = existing.iter().collect();
    find_import_duplicates(&new, &existing, Some(BANK), &FuzzyDedupConfig::default())
}

/// The rows that survive, in input order.
fn kept(new: &[Transaction], existing: &[Transaction]) -> Vec<Transaction> {
    let dropped: Vec<usize> = dedup(new, existing).iter().map(|m| m.new_index).collect();
    new.iter()
        .enumerate()
        .filter(|(i, _)| !dropped.contains(i))
        .map(|(_, t)| t.clone())
        .collect()
}

/// A canonical, order-free description of a set of rows.
fn sorted_keys(txns: &[Transaction]) -> Vec<String> {
    let mut keys: Vec<String> = txns
        .iter()
        .map(|t| {
            format!(
                "{} {:?} {:?} {:?}",
                t.date, t.narration, t.links, t.postings[0]
            )
        })
        .collect();
    keys.sort();
    keys
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// Importing the same statement twice adds nothing.
    #[test]
    fn reimporting_the_same_statement_adds_zero_rows(rows in prop::collection::vec(row(), 0..12)) {
        let txns: Vec<Transaction> = rows.iter().enumerate().map(|(i, r)| txn(i, r)).collect();
        prop_assert!(kept(&txns, &txns).is_empty());
    }

    /// Each existing transaction absorbs at most one row, so no more rows are
    /// dropped than there are existing entries; and every drop rests on an
    /// entry moving the same money.
    #[test]
    fn drops_never_exceed_matching_existing_entries(
        new in prop::collection::vec(row(), 0..12),
        existing in prop::collection::vec(row(), 0..12),
    ) {
        let new_t: Vec<Transaction> = new.iter().enumerate().map(|(i, r)| txn(i, r)).collect();
        let ex_t: Vec<Transaction> = existing.iter().enumerate().map(|(i, r)| txn(i, r)).collect();
        let dups = dedup(&new_t, &ex_t);
        let mut used: Vec<usize> = dups.iter().map(|d| d.existing_index).collect();
        used.sort_unstable();
        let before = used.len();
        used.dedup();
        prop_assert_eq!(before, used.len(), "an existing entry absorbed two rows");
        prop_assert!(dups.len() <= ex_t.len());
        for d in &dups {
            let (n, e) = (&new[d.new_index], &existing[d.existing_index]);
            prop_assert_eq!((n.1, n.2, n.3), (e.1, e.2, e.3), "{:?} matched {:?}", n, e);
        }
    }

    /// Neither the statement's row order nor the ledger's order changes HOW
    /// MANY rows survive, nor (without fuzzy-only ambiguity) WHICH rows.
    #[test]
    fn order_does_not_change_what_survives(
        new in prop::collection::vec(prop_oneof![row(), crowded_row()], 0..10),
        existing in prop::collection::vec(prop_oneof![row(), crowded_row()], 0..10),
        seed in any::<u64>(),
    ) {
        let new_t: Vec<Transaction> = new.iter().enumerate().map(|(i, r)| txn(i, r)).collect();
        let ex_t: Vec<Transaction> = existing.iter().enumerate().map(|(i, r)| txn(i, r)).collect();
        let shuffle = |v: &[Transaction], salt: u64| {
            let mut v = v.to_vec();
            let n = v.len();
            for i in (1..n).rev() {
                let j = (seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(salt + i as u64) >> 33) as usize % (i + 1);
                v.swap(i, j);
            }
            v
        };
        let base = kept(&new_t, &ex_t);
        let permuted = kept(&shuffle(&new_t, 1), &shuffle(&ex_t, 2));
        prop_assert_eq!(sorted_keys(&base), sorted_keys(&permuted));
    }

    /// Importing the first half of a statement, then the whole statement
    /// against the grown ledger, ends with each row exactly once.
    #[test]
    fn a_split_import_is_idempotent(rows in prop::collection::vec(row(), 0..12), cut in 0usize..12) {
        let txns: Vec<Transaction> = rows.iter().enumerate().map(|(i, r)| txn(i, r)).collect();
        let cut = cut.min(txns.len());
        let ledger: Vec<Transaction> = txns[..cut].to_vec();
        let second = kept(&txns, &ledger);
        prop_assert_eq!(sorted_keys(&second), sorted_keys(&txns[cut..]));
    }
}
