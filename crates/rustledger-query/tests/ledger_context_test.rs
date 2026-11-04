//! `Executor::for_ledger`, the constructor every host that runs user queries
//! goes through (#2823, #2825).
//!
//! The WASM and FFI paths built a bare executor, so the source columns and
//! `#balances.discrepancy` read NULL there while the CLI filled them. These
//! pin what the shared constructor does: source columns from the source map,
//! discrepancies from the context, and a deferred discrepancy source that
//! runs only when the compiled query reads the column.

use rustledger_loader::{BalanceDiscrepancy, SourceMap, SourceText};
use rustledger_query::executor::{BalanceDiscrepancies, LedgerContext, SummaryAccounts};
use rustledger_query::{Executor, Value, parse};
use std::sync::atomic::{AtomicUsize, Ordering};

const LEDGER: &str = "2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening
2024-01-02 *
  Assets:Bank     10 USD
  Equity:Opening
2024-01-05 balance Assets:Bank 999.00 USD
";

fn source_map() -> SourceMap {
    let mut map = SourceMap::new();
    let text: SourceText = LEDGER.into();
    map.add_file("<string>".into(), text);
    map
}

fn directives() -> Vec<rustledger_core::Spanned<rustledger_core::Directive>> {
    let parsed = rustledger_parser::parse(LEDGER);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    parsed.directives
}

/// The failing assertion in [`LEDGER`], as the balance checker reports it
/// (bean-query: `-989.00 USD`).
fn discrepancy() -> BalanceDiscrepancy {
    BalanceDiscrepancy {
        date: rustledger_core::naive_date(2024, 1, 5).expect("date"),
        account: "Assets:Bank".into(),
        amount: rustledger_core::Amount::new(rust_decimal_macros::dec!(-989.00), "USD"),
        asserted: rust_decimal_macros::dec!(999.00),
    }
}

fn context(balance_discrepancies: BalanceDiscrepancies<'_>) -> LedgerContext<'_> {
    LedgerContext {
        account_types: rustledger_core::AccountTypes::default(),
        booking_method: rustledger_core::BookingMethod::Strict,
        summary_accounts: SummaryAccounts::default(),
        balance_discrepancies,
    }
}

fn run(executor: &mut Executor<'_>, query: &str) -> Vec<Vec<Value>> {
    executor
        .execute(&parse(query).unwrap_or_else(|e| panic!("{query}: {e}")))
        .unwrap_or_else(|e| panic!("{query}: {e}"))
        .rows
}

#[test]
fn test_for_ledger_resolves_source_columns_like_bean_query() {
    let directives = directives();
    let map = source_map();
    let mut executor = Executor::for_ledger(
        &directives,
        &map,
        context(BalanceDiscrepancies::Unavailable),
    );
    let rows = run(
        &mut executor,
        "SELECT filename, lineno, location FROM postings LIMIT 1",
    );
    assert_eq!(
        rows[0],
        vec![
            Value::String("<string>".into()),
            Value::Integer(4),
            Value::String("<string>:4:".into()),
        ]
    );
    let rows = run(
        &mut executor,
        "SELECT meta('lineno'), entry_meta('filename') LIMIT 1",
    );
    assert_eq!(
        rows[0],
        vec![Value::Integer(4), Value::String("<string>".into())]
    );
}

#[test]
fn test_for_ledger_reports_known_discrepancies() {
    let directives = directives();
    let map = source_map();
    let mut executor = Executor::for_ledger(
        &directives,
        &map,
        context(BalanceDiscrepancies::Known(vec![discrepancy()])),
    );
    let rows = run(&mut executor, "SELECT account, discrepancy FROM #balances");
    assert_eq!(rows[0][1], Value::Amount(discrepancy().amount));
}

/// A deferred source runs only when the compiled query reads the column, at
/// most once per executor; a query that does not read it costs nothing.
#[test]
fn test_for_ledger_computes_lazy_discrepancies_only_when_read() {
    let directives = directives();
    let map = source_map();
    let calls = AtomicUsize::new(0);
    let lazy = || {
        BalanceDiscrepancies::Lazy(Box::new(|| {
            calls.fetch_add(1, Ordering::SeqCst);
            vec![discrepancy()]
        }))
    };

    for query in [
        "SELECT account, amount FROM #balances",
        "SELECT count(*) FROM #balances",
        "SELECT account FROM postings",
        "SELECT * FROM #prices",
    ] {
        let mut executor = Executor::for_ledger(&directives, &map, context(lazy()));
        run(&mut executor, query);
        assert_eq!(calls.load(Ordering::SeqCst), 0, "{query} does not read it");
    }

    for query in [
        "SELECT account, discrepancy FROM #balances",
        "SELECT * FROM #balances",
        "SELECT account FROM #balances WHERE discrepancy IS NOT NULL",
        "SELECT a FROM (SELECT account AS a, discrepancy FROM #balances)",
    ] {
        calls.store(0, Ordering::SeqCst);
        let mut executor = Executor::for_ledger(&directives, &map, context(lazy()));
        let rows = run(&mut executor, query);
        assert_eq!(calls.load(Ordering::SeqCst), 1, "{query} reads it");
        assert!(!rows.is_empty(), "{query}");
        // A second query on the same executor reuses the first answer.
        run(&mut executor, query);
        assert_eq!(
            calls.load(Ordering::SeqCst),
            1,
            "{query}: once per executor"
        );
    }
}

/// Spans kept beside plain directives are put back for the query; a ledger
/// whose spans did not survive (a cache that carries none) reads NULL rather
/// than another directive's line.
#[test]
fn test_spanned_from_parts_synthesizes_when_spans_are_missing() {
    let spanned = directives();
    let plain: Vec<_> = spanned.iter().map(|s| s.value.clone()).collect();
    let spans: Vec<_> = spanned.iter().map(|s| (s.span, s.file_id)).collect();

    let back = rustledger_query::executor::spanned_from_parts(&plain, &spans);
    assert_eq!(back, spanned);

    let missing = rustledger_query::executor::spanned_from_parts(&plain, &spans[1..]);
    assert!(
        missing
            .iter()
            .all(|s| s.file_id == rustledger_core::SYNTHESIZED_FILE_ID)
    );
}

/// A pad's synthesized transaction is located where beancount locates it
/// (bean-query 0.2.0 on this ledger): the entry at the `pad` line (4) in
/// `#entries`, and its postings at the `balance` line (8) in the postings
/// table. It read an empty filename and line 0 before.
#[test]
fn test_for_ledger_locates_a_pad_transaction_like_bean_query() {
    let ledger = "2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening

2024-01-02 pad Assets:Bank Equity:Opening



2024-01-05 balance Assets:Bank 100.00 USD
";
    let parsed = rustledger_parser::parse(ledger);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let directives = rustledger_booking::merge_with_padding_spanned(&parsed.directives);
    let mut map = SourceMap::new();
    let text: SourceText = ledger.into();
    map.add_file("<string>".into(), text);
    let mut executor = Executor::for_ledger(
        &directives,
        &map,
        context(BalanceDiscrepancies::Unavailable),
    );

    let rows = run(
        &mut executor,
        "SELECT type, lineno FROM #entries WHERE type = 'transaction'",
    );
    assert_eq!(
        rows,
        vec![vec![Value::String("transaction".into()), Value::Integer(4)]]
    );

    let rows = run(
        &mut executor,
        "SELECT lineno, location, account FROM postings",
    );
    assert_eq!(
        rows,
        vec![
            vec![
                Value::Integer(8),
                Value::String("<string>:8:".into()),
                Value::String("Assets:Bank".into()),
            ],
            vec![
                Value::Integer(8),
                Value::String("<string>:8:".into()),
                Value::String("Equity:Opening".into()),
            ],
        ]
    );
}
