//! Integration tests for `Ledger::balance_view()`.
//!
//! Pins the two architectural guarantees:
//!
//! 1. `Ledger.directives` is **source-faithful**: `Pad` directives
//!    survive the load pipeline as `Pad` directives.
//! 2. `Ledger.balance_view()` returns a **derived view**: pads are
//!    merged with synthesized `P`-flag transactions suitable for
//!    inventory math.
//!
//! Together these tests pin the source-vs-derived split that the
//! `refactor/pad-source-faithful-directives` architecture rests on.
//! A regression that pre-expands at the loader (PR #1301's step 10)
//! would fail (1); a regression that drops the expansion entirely
//! would fail (2).

use rustledger_core::Directive;
use rustledger_loader::{LoadOptions, load};
use std::io::Write;

/// The canonical #1288 fixture: one pad+balance pair, expected
/// `Assets:Wallet` ends at 965 USD = 1000 (opening) - 10 (Jun 1
/// expense) - 15 (pad: 990 → 975) - 10 (Jun 2 expense).
const PADDED_SOURCE: &str = r#"option "operating_currency" "USD"

2026-01-01 open Assets:Wallet USD
2026-01-01 open Equity:Void USD
2026-01-01 open Expenses:Expense USD

2026-01-01 * "opening"
  Assets:Wallet  1000 USD
  Equity:Void

2026-06-01 * "expense"
  Expenses:Expense  10 USD
  Assets:Wallet

2026-06-01 pad Assets:Wallet Equity:Void
2026-06-02 balance Assets:Wallet 975 USD

2026-06-02 * "expense"
  Expenses:Expense  10 USD
  Assets:Wallet
"#;

fn write_fixture(content: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("balance-view-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(content.as_bytes()).expect("write fixture");
    f
}

/// `Ledger.directives` keeps `Pad` directives as `Pad`. The loader
/// must NOT pre-expand them into synthesized transactions — that's
/// what `balance_view()` is for.
#[test]
fn directives_field_keeps_pads_as_pads() {
    let fixture = write_fixture(PADDED_SOURCE);
    let opts = LoadOptions {
        validate: false,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");

    let pad_count = ledger
        .directives
        .iter()
        .filter(|s| matches!(s.value, Directive::Pad(_)))
        .count();
    assert_eq!(
        pad_count, 1,
        "Ledger.directives must keep Pads as Pads (source-faithful). \
         A loader-side expansion regression would make this 0."
    );

    // Synth P-flag transactions must NOT be in the source view.
    let p_flag_count = ledger
        .directives
        .iter()
        .filter(|s| matches!(&s.value, Directive::Transaction(t) if t.flag == 'P'))
        .count();
    assert_eq!(
        p_flag_count, 0,
        "Ledger.directives must NOT contain synth P-flag transactions \
         (those are the derived view). A loader-side pre-expansion \
         would put one here."
    );
}

/// `Ledger.balance_view()` returns the merged view: original
/// directives preserved verbatim, AND synthesized P-flag
/// transactions added for each pad-balance pair.
///
/// Preserving Pads in the view matters for BQL queries that filter
/// on `WHERE type = 'pad'` (Python-compat) and for the multi-pad
/// shadowing correctness (#1300). Inventory-walking consumers
/// iterate `Directive::Transaction` and ignore Pads, so the
/// preserved Pads are invisible to balance math.
#[test]
fn balance_view_adds_synth_transaction_alongside_original_pad() {
    let fixture = write_fixture(PADDED_SOURCE);
    let opts = LoadOptions {
        validate: false,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");
    let view = ledger.balance_view();

    let pad_count = view
        .iter()
        .filter(|d| matches!(d, Directive::Pad(_)))
        .count();
    assert_eq!(
        pad_count, 1,
        "balance_view() must preserve the original Pad directive so \
         BQL `WHERE type = 'pad'` queries continue to match it.",
    );

    let synth_count = view
        .iter()
        .filter(|d| matches!(d, Directive::Transaction(t) if t.flag == 'P'))
        .count();
    assert_eq!(
        synth_count, 1,
        "balance_view() must contain exactly one synthesized P-flag \
         transaction representing the pad's effect."
    );
}

/// `balance_view()` is a pure function of `directives`: calling it
/// repeatedly yields equivalent results, and the source view is
/// unchanged after the call.
#[test]
fn balance_view_does_not_mutate_source_directives() {
    let fixture = write_fixture(PADDED_SOURCE);
    let opts = LoadOptions {
        validate: false,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");

    let len_before = ledger.directives.len();
    let _ = ledger.balance_view();
    let len_after = ledger.directives.len();

    assert_eq!(
        len_before, len_after,
        "balance_view() must not change the length of self.directives"
    );
    let pads_after = ledger
        .directives
        .iter()
        .filter(|s| matches!(s.value, Directive::Pad(_)))
        .count();
    assert_eq!(
        pads_after, 1,
        "balance_view() must not remove or transform Pads in self.directives"
    );
}

/// On a pad-free ledger, `balance_view()` returns the same shape as
/// `directives` (modulo Spanned stripping): no spurious synth
/// transactions, no dropped directives. This guards against an
/// expand-pads regression that emits ghost transactions on
/// pad-free input.
#[test]
fn balance_view_on_pad_free_ledger_is_equivalent_to_directives() {
    const PAD_FREE: &str = r#"option "operating_currency" "USD"

2026-01-01 open Assets:Wallet USD
2026-01-01 open Equity:Void USD

2026-01-01 * "opening"
  Assets:Wallet  1000 USD
  Equity:Void
"#;
    let fixture = write_fixture(PAD_FREE);
    let opts = LoadOptions {
        validate: false,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");
    let view = ledger.balance_view();

    assert_eq!(
        view.len(),
        ledger.directives.len(),
        "balance_view() must have the same length as directives on \
         pad-free input (no spurious synth, no drops)."
    );

    let synth_count = view
        .iter()
        .filter(|d| matches!(d, Directive::Transaction(t) if t.flag == 'P'))
        .count();
    assert_eq!(
        synth_count, 0,
        "balance_view() must not emit synth P-flag transactions on \
         pad-free input."
    );
}

/// The padding `units` the balance view and the validator inserts for
/// `source`, and whether validation reports the pad unused (`E2003`).
fn padding_and_unused(source: &str) -> (Vec<String>, bool) {
    let fixture = write_fixture(source);
    let opts = LoadOptions {
        validate: true,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");
    let padding = ledger
        .balance_view()
        .iter()
        .filter_map(|d| match d {
            Directive::Transaction(t) if rustledger_booking::is_synthesized_pad(t) => t.postings[0]
                .amount()
                .map(|a| format!("{} {}", a.number, a.currency)),
            _ => None,
        })
        .collect();
    let unused = ledger.errors.iter().any(|e| e.code == "E2003");
    (padding, unused)
}

const TOLERANCE_PAD: &str = "2024-01-01 open Assets:A
2024-01-01 open Equity:O
2024-01-02 * \"x\"
  Assets:A  99.97 USD
  Equity:O  -99.97 USD
2024-01-03 pad Assets:A Equity:O
2024-01-10 balance Assets:A 100.00 USD
";

/// The ledger's `tolerance_multiplier` reaches the pad rule, in the balance
/// view and in validation alike (#2901). Verified with bean-check and
/// bean-query 3.2.3: under `option "tolerance_multiplier" "2"` the 0.03
/// difference is within 2 * 2 * 0.01, so nothing is padded and the pad is
/// an `Unused Pad entry`; at the default 0.5 it pads 0.03.
#[test]
fn test_balance_view_pads_with_the_ledgers_tolerance_multiplier() {
    let (padding, unused) = padding_and_unused(&format!(
        "option \"tolerance_multiplier\" \"2\"\n{TOLERANCE_PAD}"
    ));
    assert!(padding.is_empty(), "nothing is padded: {padding:?}");
    assert!(unused, "the pad is unused");

    let (padding, unused) = padding_and_unused(TOLERANCE_PAD);
    assert_eq!(padding, ["0.03 USD"]);
    assert!(!unused);
}

/// `inferred_tolerance_default` does not widen a balance's tolerance, so
/// the pad still pads (bean-query 3.2.3: 0.03 USD under
/// `option "inferred_tolerance_default" "USD:0.05"`, bean-check clean).
#[test]
fn test_balance_view_pad_ignores_inferred_tolerance_default() {
    let (padding, unused) = padding_and_unused(&format!(
        "option \"inferred_tolerance_default\" \"USD:0.05\"\n{TOLERANCE_PAD}"
    ));
    assert_eq!(padding, ["0.03 USD"]);
    assert!(!unused);
}

/// A loaded ledger keeps its directives in booking order, which puts a
/// `pad` ahead of the same date's `note`; the pad rule ranks accounts by
/// their source location instead, as beancount's entry order does (#2901).
/// bean-check 3.2.3 prints `(1 CCC, 1 DDD, ...)` for this ledger: the note
/// meets `Assets:A:C` before the pad meets `Assets:A:D`.
#[test]
fn test_loaded_pad_ranks_accounts_in_beancount_entry_order() {
    let fixture = write_fixture(
        "2023-12-31 note Assets:A:C \"n\"\n2023-12-31 pad Assets:Z Assets:A:D\n\
         2024-01-01 open Assets:A\n2024-01-01 open Assets:A:C\n2024-01-01 open Assets:A:D\n\
         2024-01-01 open Assets:Z\n2024-01-01 open Assets:Cash\n2024-01-01 open Equity:O\n\
         2024-02-01 * \"lot\"\n  Assets:A  10 STK {10 USD}\n  Assets:Cash  -100 USD\n\
         2024-02-02 * \"g\"\n  Assets:A:C  1 CCC\n  Assets:A:D  1 DDD\n  Equity:O  -1 CCC\n\
         \x20 Equity:O  -1 DDD\n2024-02-03 pad Assets:A Equity:O\n\
         2024-02-10 balance Assets:A 11 STK\n",
    );
    let opts = LoadOptions {
        validate: true,
        ..Default::default()
    };
    let ledger = load(fixture.path(), &opts).expect("load");
    let messages: Vec<&str> = ledger
        .errors
        .iter()
        .filter(|e| e.code == "E2005")
        .map(|e| e.message.as_str())
        .collect();
    assert_eq!(
        messages,
        [
            "Attempt to pad an entry with cost for balance: (1 CCC, 1 DDD, 10 STK {10 USD, 2024-02-01})"
        ]
    );
}

/// The "Attempt to pad an entry with cost" messages of the ledger at `path`.
fn pad_at_cost_messages(path: &std::path::Path) -> Vec<String> {
    let opts = LoadOptions {
        validate: true,
        ..Default::default()
    };
    let ledger = load(path, &opts).expect("load");
    ledger
        .errors
        .iter()
        .filter(|e| e.code == "E2005")
        .map(|e| e.message.clone())
        .collect()
}

const RANK_TAIL: &str =
    "2024-02-01 * \"lot\"\n  Assets:A  10 STK {10 USD}\n  Assets:Cash  -100 USD\n";
const RANK_END: &str = "2024-02-02 * \"g\"\n  Assets:A:C  1 CCC\n  Assets:A:D  1 DDD\n\
    \x20 Equity:O  -1 CCC\n  Equity:O  -1 DDD\n2024-02-03 pad Assets:A Equity:O\n\
    2024-02-10 balance Assets:A 11 STK\n";
const D_FIRST: &str =
    "Attempt to pad an entry with cost for balance: (1 DDD, 1 CCC, 10 STK {10 USD, 2024-02-01})";

/// Beancount's entry order reads the line number whichever file it is in
/// (#2901): `Assets:A:D` opened on line 1 of an included file comes before
/// `Assets:A:C` opened on line 5 of the main file. bean-check 3.2.3 prints
/// `(1 DDD, 1 CCC, ...)`.
#[test]
fn test_pad_ranks_accounts_by_line_across_files() {
    let dir = tempfile::tempdir().expect("tempdir");
    // A long first line puts the open past the main file's `Assets:A:C` by
    // byte offset, though not by line: only the line decides.
    let long = format!("; {}\n2024-01-01 open Assets:A:D\n", "x".repeat(300));
    std::fs::write(dir.path().join("inc.beancount"), long).expect("write");
    let main = dir.path().join("main.beancount");
    std::fs::write(
        &main,
        format!(
            "include \"inc.beancount\"\n2024-01-01 open Assets:A\n2024-01-01 open Assets:Cash\n\
             2024-01-01 open Equity:O\n2024-01-01 open Assets:A:C\n{RANK_TAIL}{RANK_END}"
        ),
    )
    .expect("write");
    assert_eq!(pad_at_cost_messages(&main), [D_FIRST]);
}

/// A plugin's entry has the line the plugin gives it in beancount's entry
/// order (#2901): the `open` `auto_accounts` makes for `Assets:A:D` is line
/// 2 (its account's place in the sorted list), before the written same-date
/// `open` of `Assets:A:C` on line 8. bean-check 3.2.3 prints
/// `(1 DDD, 1 CCC, ...)`.
#[test]
fn test_pad_ranks_a_plugins_open_first() {
    let fixture = write_fixture(&format!(
        "plugin \"beancount.plugins.auto_accounts\"\n2024-01-01 open Assets:A\n\
         2024-01-01 open Assets:Cash\n2024-01-01 open Equity:O\n{RANK_TAIL}\
         2024-02-02 open Assets:A:C\n{RANK_END}"
    ));
    assert_eq!(pad_at_cost_messages(fixture.path()), [D_FIRST]);
}

/// Write `files` (name, text) into a fresh directory; the main file is the
/// first. Returns the directory and the main file's path.
fn write_ledger(files: &[(&str, &str)]) -> (tempfile::TempDir, std::path::PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    for (name, text) in files {
        std::fs::write(dir.path().join(name), text).expect("write");
    }
    let main = dir.path().join(files[0].0);
    (dir, main)
}

/// The tail of a ledger whose pad onto `Assets:A` reports the positions of
/// `Assets:A:<X>`, `Assets:A:<Y>`, `Assets:A:<Z>` in the order its group
/// first meets them.
fn three_account_tail(accounts: [&str; 3]) -> String {
    let [x, y, z] = accounts;
    let unit = |a: &str| a.repeat(3);
    format!(
        "2024-01-01 open Assets:A\n2024-01-01 open Assets:Cash\n2024-01-01 open Equity:O\n\
         {RANK_TAIL}2024-02-02 * \"g\"\n  Assets:A:{x}  1 {}\n  Assets:A:{y}  1 {}\n\
         \x20 Assets:A:{z}  1 {}\n  Equity:O  -1 {}\n  Equity:O  -1 {}\n  Equity:O  -1 {}\n\
         2024-02-03 pad Assets:A Equity:O\n2024-02-10 balance Assets:A 11 STK\n",
        unit(x),
        unit(y),
        unit(z),
        unit(x),
        unit(y),
        unit(z),
    )
}

/// Beancount's entry order breaks a tie on the line by the order it parsed
/// the files in (#2901): the main file, then its include, then that file's
/// include. Each opens one account on line 2. bean-check 3.2.3 prints
/// `(1 CCC, 1 DDD, 1 EEE, ...)`.
#[test]
fn test_pad_ranks_a_tied_line_by_file_through_a_nested_include() {
    let main = format!(
        "include \"a.beancount\"\n2024-01-01 open Assets:A:C\n{}",
        three_account_tail(["C", "D", "E"])
    );
    let (_dir, path) = write_ledger(&[
        ("main.beancount", &main),
        (
            "a.beancount",
            "include \"b.beancount\"\n2024-01-01 open Assets:A:D\n",
        ),
        ("b.beancount", "; b\n2024-01-01 open Assets:A:E\n"),
    ]);
    assert_eq!(
        pad_at_cost_messages(&path),
        ["Attempt to pad an entry with cost for balance: \
          (1 CCC, 1 DDD, 1 EEE, 10 STK {10 USD, 2024-02-01})"]
    );
}

/// A same-date `note` on line 1 of the main file meets its account before a
/// `pad` on line 1 of an include meets its own (#2901): the tie on the line
/// goes to the file parsed first, though the booking order puts the pad
/// ahead of the note. bean-check 3.2.3 prints `(1 CCC, 1 DDD, ...)`, and
/// with the two swapped, `(1 DDD, 1 CCC, ...)`.
#[test]
fn test_pad_ranks_a_tied_line_by_file_not_by_booking_order() {
    let note = "2023-12-31 note Assets:A:C \"n\"\n";
    let pad = "2023-12-31 pad Assets:Z Assets:A:D\n";
    let rest = "2024-01-01 open Assets:A\n2024-01-01 open Assets:A:C\n\
        2024-01-01 open Assets:A:D\n2024-01-01 open Assets:Z\n\
        2024-01-01 open Assets:Cash\n2024-01-01 open Equity:O\n";
    for (in_main, in_include, expected) in [
        (note, pad, "(1 CCC, 1 DDD, 10 STK {10 USD, 2024-02-01})"),
        (pad, note, "(1 DDD, 1 CCC, 10 STK {10 USD, 2024-02-01})"),
    ] {
        let main = format!("{in_main}include \"inc.beancount\"\n{rest}{RANK_TAIL}{RANK_END}");
        let (_dir, path) =
            write_ledger(&[("main.beancount", &main), ("inc.beancount", in_include)]);
        assert_eq!(
            pad_at_cost_messages(&path),
            [format!(
                "Attempt to pad an entry with cost for balance: {expected}"
            )]
        );
    }
}

/// Beancount parses its files breadth first (the main file's includes, then
/// theirs) and a tie on the line goes by that order (#2936); the loader
/// reads depth first, but ranks the files breadth first
/// (`SourceMap::parse_ranks`). `x.beancount` includes `z.beancount`, and the
/// main file includes `x` then `y`; each opens one account on line 2.
/// bean-check 3.2.3 prints `(1 XXX, 1 YYY, 1 ZZZ, ...)`; depth first was
/// `(1 XXX, 1 ZZZ, 1 YYY, ...)`.
#[test]
fn test_pad_ranks_a_tied_line_by_beancounts_breadth_first_file_order() {
    let main = format!(
        "include \"x.beancount\"\ninclude \"y.beancount\"\n{}",
        three_account_tail(["X", "Y", "Z"])
    );
    let (_dir, path) = write_ledger(&[
        ("main.beancount", &main),
        (
            "x.beancount",
            "include \"z.beancount\"\n2024-01-01 open Assets:A:X\n",
        ),
        ("y.beancount", "; y\n2024-01-01 open Assets:A:Y\n"),
        ("z.beancount", "; z\n2024-01-01 open Assets:A:Z\n"),
    ]);
    assert_eq!(
        pad_at_cost_messages(&path),
        ["Attempt to pad an entry with cost for balance: \
          (1 XXX, 1 YYY, 1 ZZZ, 10 STK {10 USD, 2024-02-01})"]
    );
}

use std::fmt::Write as _;

/// A ledger of `files`, `(name, includes)` with the main file first: each
/// file other than the main one writes its includes, then opens
/// `Assets:A:<NAME>` (its file name's stem, upper-cased) on line 9, so
/// every open ties on the line. The main file writes its includes, then a
/// pad onto `Assets:A` whose "Attempt to pad an entry with cost" lists
/// those accounts in the order beancount meets them.
fn include_tree(files: &[(&str, &[&str])]) -> (tempfile::TempDir, std::path::PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut accounts = Vec::new();
    let mut main = String::new();
    for (index, (name, includes)) in files.iter().enumerate() {
        let mut text = String::new();
        for i in *includes {
            let _ = writeln!(text, "include \"{i}\"");
        }
        if index == 0 {
            main = text;
            continue;
        }
        let stem = std::path::Path::new(name)
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_uppercase();
        text.push_str(&"; pad\n".repeat(8 - includes.len()));
        let _ = writeln!(text, "2024-01-01 open Assets:A:{stem}");
        let path = dir.path().join(name);
        std::fs::create_dir_all(path.parent().unwrap()).expect("mkdir");
        std::fs::write(path, text).expect("write");
        accounts.push(stem);
    }
    main.push_str(&"; pad\n".repeat(19 - files[0].1.len()));
    main.push_str(
        "2024-01-01 open Assets:A\n2024-01-01 open Assets:Cash\n2024-01-01 open Equity:O\n",
    );
    main.push_str(RANK_TAIL);
    main.push_str("2024-02-02 * \"g\"\n");
    for a in &accounts {
        let _ = writeln!(main, "  Assets:A:{a}  1 {}", a.repeat(3));
    }
    for a in &accounts {
        let _ = writeln!(main, "  Equity:O  -1 {}", a.repeat(3));
    }
    main.push_str("2024-02-03 pad Assets:A Equity:O\n2024-02-10 balance Assets:A 11 STK\n");
    let path = dir.path().join(files[0].0);
    std::fs::write(&path, main).expect("write");
    (dir, path)
}

/// The "Attempt to pad an entry with cost" listing one of each of `units`
/// then the lot.
fn tied_message(units: &[&str]) -> String {
    let units: Vec<String> = units.iter().map(|u| format!("1 {u}")).collect();
    format!(
        "Attempt to pad an entry with cost for balance: ({}, 10 STK {{10 USD, 2024-02-01}})",
        units.join(", ")
    )
}

/// #2936 on a three-level tree: `main` includes `a`, `b`; `a` includes
/// `c`, `d`; `b` includes `f`; `c` includes `e`. bean-check 3.2.3 prints
/// `(1 AAA, 1 BBB, 1 CCC, 1 DDD, 1 FFF, 1 EEE, ...)`; depth first would be
/// `AAA, CCC, EEE, DDD, BBB, FFF`.
#[test]
fn test_pad_ranks_a_three_level_include_tree_breadth_first() {
    let (_dir, path) = include_tree(&[
        ("main.beancount", &["a.beancount", "b.beancount"]),
        ("a.beancount", &["c.beancount", "d.beancount"]),
        ("b.beancount", &["f.beancount"]),
        ("c.beancount", &["e.beancount"]),
        ("d.beancount", &[]),
        ("e.beancount", &[]),
        ("f.beancount", &[]),
    ]);
    assert_eq!(
        pad_at_cost_messages(&path),
        [tied_message(&["AAA", "BBB", "CCC", "DDD", "FFF", "EEE"])]
    );
}

/// #2936: a file included twice ranks by the include breadth first meets
/// first. `main` includes `a`, `b`; `a` includes `c`; `c` includes `b`
/// again, where the loader reads it, depth first. bean-check 3.2.3 parses
/// `b` from `main`, reports the other include as `Duplicate filename
/// parsed`, and prints `(1 AAA, 1 BBB, 1 CCC, ...)`; depth first would be
/// `AAA, CCC, BBB`. With `c` including `a` too (a cycle), the same.
#[test]
fn test_pad_ranks_a_duplicate_or_cyclic_include_where_beancount_parses_it() {
    for c_includes in [&["b.beancount"][..], &["a.beancount", "b.beancount"]] {
        let (_dir, path) = include_tree(&[
            ("main.beancount", &["a.beancount", "b.beancount"]),
            ("a.beancount", &["c.beancount"]),
            ("b.beancount", &[]),
            ("c.beancount", c_includes),
        ]);
        assert_eq!(
            pad_at_cost_messages(&path),
            [tied_message(&["AAA", "BBB", "CCC"])],
            "c includes {c_includes:?}"
        );
    }
}

/// #2936 through a glob: `main` includes `g/*.beancount` (`g/p`, `g/q`)
/// then `y`, and `g/p` includes `z`. Breadth first is `P, Q, Y, Z`; depth
/// first would be `P, Z, Q, Y`. bean-check 3.2.3 agrees but for the order
/// of the glob's own matches, which it takes from `glob.glob` unsorted (the
/// directory's order: `QQQ, PPP` on the machine checked); the loader sorts
/// them.
#[test]
fn test_pad_ranks_a_globs_matches_ahead_of_their_includes() {
    let (_dir, path) = include_tree(&[
        ("main.beancount", &["g/*.beancount", "y.beancount"]),
        ("g/p.beancount", &["../z.beancount"]),
        ("g/q.beancount", &[]),
        ("y.beancount", &[]),
        ("z.beancount", &[]),
    ]);
    assert_eq!(
        pad_at_cost_messages(&path),
        [tied_message(&["PPP", "QQQ", "YYY", "ZZZ"])]
    );
}

/// An `open` `auto_accounts` makes has the line the plugin numbers it with,
/// its account's place among every account the ledger names (#2901), and
/// comes ahead of a written `open` tied with it: `Assets:A:B1` is 1, ahead
/// of the written `Assets:A:C` on line 1; `Assets:A:B2` is 2 and
/// `Assets:A:D` 4. bean-check 3.2.3 prints
/// `(1 B1X, 1 CCC, 1 B2X, 1 DDD, ...)`.
#[test]
fn test_pad_ranks_a_plugins_open_by_the_line_the_plugin_gives_it() {
    let fixture = write_fixture(&format!(
        "2024-02-02 open Assets:A:C\nplugin \"beancount.plugins.auto_accounts\"\n\
         2024-01-01 open Assets:A\n2024-01-01 open Assets:Cash\n2024-01-01 open Equity:O\n\
         {RANK_TAIL}2024-02-02 * \"g\"\n  Assets:A:C  1 CCC\n  Assets:A:D  1 DDD\n\
         \x20 Assets:A:B1  1 B1X\n  Assets:A:B2  1 B2X\n  Equity:O  -1 CCC\n\
         \x20 Equity:O  -1 DDD\n  Equity:O  -1 B1X\n  Equity:O  -1 B2X\n\
         2024-02-03 pad Assets:A Equity:O\n2024-02-10 balance Assets:A 11 STK\n"
    ));
    assert_eq!(
        pad_at_cost_messages(fixture.path()),
        ["Attempt to pad an entry with cost for balance: \
          (1 B1X, 1 CCC, 1 B2X, 1 DDD, 10 STK {10 USD, 2024-02-01})"]
    );
}
