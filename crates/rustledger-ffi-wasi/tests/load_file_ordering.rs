//! Regression guard for #1991: the MULTI-FILE load surface must emit a
//! globally date-sorted stream, including the top-level file's own directives.
//!
//! `load_source_sorts_directives_by_date` next door pins the same property for
//! the single-source surface. Nothing pinned it for `load_file`, which is the
//! path with `include` resolution — and that is the one that broke.
//!
//! What broke, on rustledger v0.11.0 (shipped in rustfava 1.30.12): the FFI had
//! its own hand-rolled parse-and-book path rather than the loader's
//! `sort → synth → book → regular → finalize` pipeline, and nothing sorted at
//! any layer. The stream came out in include-expansion order — every included
//! file's entries, then the top-level file's own directives in FILE order:
//!
//! ```text
//!   ... Transaction 2022-06-30      <- last included file
//!   Transaction 2020-10-01          <- the top-level file's own, in file order
//!   Open        2020-10-01 ...      <- and its opens
//! ```
//!
//! A consumer scanning backwards for "the last entry" then reads an early date.
//! The reporter's rustfava collapsed a two-year ledger to a single month.
//!
//! It is fixed, but INCIDENTALLY — the FFI stopped being unsorted because it
//! was rerouted onto the canonical pipeline, not because anyone set out to fix
//! ordering. An incidental fix with no guard is one refactor from coming back,
//! which is what this file is for.
//!
//! # What these tests can and cannot distinguish
//!
//! Two sorts stand between this fixture and an unordered stream, and they are
//! REDUNDANT for it: the pipeline's first phase (`Directives::sort`) and
//! `finalize`'s re-sort after the plugin passes. Removing either alone changes
//! nothing here, so a reader should not take a green run as evidence that both
//! are load-bearing. Measured by deleting them:
//!
//! ```text
//!   remove finalize's sort only          -> all pass
//!   remove the pipeline sort only        -> all pass
//!   remove BOTH (the v0.11.0 state)      -> 2 of 3 FAIL
//!   remove expand_pads' sort             -> the pad test FAILS
//! ```
//!
//! That is depth rather than vacuity — the state these guard against is the one
//! that shipped, and they catch it. But if a future change makes one sort the
//! only one, these will not notice the other going missing, and something
//! narrower would be needed to pin each.

use std::io::Write;
use std::path::{Path, PathBuf};

use rustledger_core::Directive;
use rustledger_ffi_wasi::helpers::{expand_pads, load_file};

/// `load_file`'s second positional argument. Named because a bare `true` next
/// to a file about `expand_pads=true` reads as the wrong flag entirely.
const CONFINE_INCLUDES: bool = true;

fn write(dir: &Path, name: &str, body: &str) -> PathBuf {
    let path = dir.join(name);
    let mut file = std::fs::File::create(&path).expect("create fixture");
    file.write_all(body.as_bytes()).expect("write fixture");
    path
}

/// The reported shape: a top-level file that `include`s monthly journals AND
/// declares directives of its own — one transaction dated at the very start of
/// history, followed by many `open`s.
///
/// The top-level transaction is placed AFTER the includes in file order, which
/// is what put it last in the unsorted stream. The `open`s matter too: they are
/// the tell, because any date sort puts them at the front, so finding them at
/// the end means nothing sorted at all.
fn write_reported_shape(dir: &Path) -> PathBuf {
    let mut includes = String::new();
    let (mut year, mut month) = (2020u32, 10u32);
    for i in 0..21 {
        let name = format!("m{i:02}.beancount");
        let mut body = String::new();
        for day in [1u32, 15, 28] {
            body.push_str(&format!(
                "{year}-{month:02}-{day:02} * \"t{i}-{day}\"\n  \
                 Assets:Bank  -1.00 USD\n  Expenses:Food  1.00 USD\n\n"
            ));
        }
        write(dir, &name, &body);
        includes.push_str(&format!("include \"{name}\"\n"));
        (year, month) = if month == 12 {
            (year + 1, 1)
        } else {
            (year, month + 1)
        };
    }

    let mut main = includes;
    main.push_str(
        "\n2020-10-01 * \"top-level transaction\"\n  \
         Assets:Bank  -5.00 USD\n  Expenses:Food  5.00 USD\n\n",
    );
    main.push_str("2020-10-01 open Assets:Bank USD\n2020-10-01 open Expenses:Food USD\n");
    for i in 0..130 {
        main.push_str(&format!("2020-10-01 open Assets:Acct{i} USD\n"));
    }
    write(dir, "main.beancount", &main)
}

/// The first place the stream stops being date-ordered, if any.
fn first_inversion(directives: &[Directive]) -> Option<(usize, String, String)> {
    directives.windows(2).enumerate().find_map(|(i, w)| {
        (w[0].date() > w[1].date()).then(|| (i, w[0].date().to_string(), w[1].date().to_string()))
    })
}

#[test]
fn load_file_emits_a_globally_date_sorted_stream() {
    let dir = tempfile::tempdir().expect("tempdir");
    let main = write_reported_shape(dir.path());

    let loaded = load_file(&main, CONFINE_INCLUDES).expect("fixture loads");

    assert!(
        loaded.directives.len() > 150,
        "fixture must actually load the include tree; got {} directives",
        loaded.directives.len(),
    );
    assert_eq!(
        first_inversion(&loaded.directives),
        None,
        "load_file must emit a globally date-sorted stream (#1991)",
    );
}

/// The top-level file's own early transaction must not be at the END.
///
/// Asserted separately from sortedness because it is the SYMPTOM the report
/// described, and it is what a consumer actually depends on: rustfava scans
/// backwards for the last `Transaction` to derive the default date range, so an
/// early entry sitting last silently shortens the range rather than erroring.
#[test]
fn the_top_level_files_own_entry_is_not_stranded_at_the_end() {
    let dir = tempfile::tempdir().expect("tempdir");
    let main = write_reported_shape(dir.path());

    let loaded = load_file(&main, CONFINE_INCLUDES).expect("fixture loads");

    let last_transaction_date = loaded
        .directives
        .iter()
        .rev()
        .find_map(|d| match d {
            Directive::Transaction(t) => Some(t.date),
            _ => None,
        })
        .expect("the fixture has transactions");
    let max_transaction_date = loaded
        .directives
        .iter()
        .filter_map(|d| match d {
            Directive::Transaction(t) => Some(t.date),
            _ => None,
        })
        .max()
        .expect("the fixture has transactions");

    assert_eq!(
        last_transaction_date, max_transaction_date,
        "scanning backwards for the last transaction must find the LATEST one; \
         finding {last_transaction_date} while the ledger runs to \
         {max_transaction_date} is the #1991 shape, and it shortens a \
         consumer's date range silently",
    );
}

/// The pad-expanded stream stays sorted too.
///
/// This is the path the reporter was actually on: rustfava calls `load-file`
/// with `expand_pads=true`, which prepends synthesized transactions and
/// re-sorts. Pinned separately because it sorts by a DIFFERENT key — `d.date()`
/// alone, rather than the loader's `canonical_sort_key` — so it is its own
/// opportunity to lose the ordering, and the fixture reaches it only here.
#[test]
fn the_pad_expanded_stream_is_also_globally_sorted() {
    let dir = tempfile::tempdir().expect("tempdir");
    // A pad + balance, so expansion has something to synthesize.
    let mut extra = String::from(
        "2020-10-01 open Assets:Pad USD\n2020-10-01 open Equity:Opening USD\n\
         2020-11-01 pad Assets:Pad Equity:Opening\n\
         2020-12-01 balance Assets:Pad  100.00 USD\n",
    );
    let main = write_reported_shape(dir.path());
    extra.insert_str(0, &std::fs::read_to_string(&main).expect("read main"));
    std::fs::write(&main, extra).expect("rewrite main");

    let loaded = load_file(&main, CONFINE_INCLUDES).expect("fixture loads");
    // `(line, file)` tags, matching `convert.rs`'s real call rather than a
    // simpler stand-in. `expand_pads` is generic over the tag, so a line-only
    // `u32` compiles and passes — and would not be exercising what this test
    // claims to: the MULTI-FILE surface, where the tag carries the originating
    // file too. Copilot's catch.
    let tags: Vec<(u32, String)> = loaded
        .directive_lines
        .iter()
        .copied()
        .zip(loaded.directive_files.iter().cloned())
        .collect();
    let synth_tag = (0u32, "<synthesized>".to_string());
    let (expanded, expanded_tags) = expand_pads(loaded.directives, tags, &synth_tag);

    assert_eq!(
        expanded.len(),
        expanded_tags.len(),
        "every directive must keep a tag through expansion",
    );
    assert!(
        expanded_tags
            .iter()
            .any(|(_, file)| file.ends_with("m00.beancount")),
        "the tags must carry originating FILES, or this is not exercising the \
         multi-file surface: {:?}",
        expanded_tags.first(),
    );

    assert!(
        expanded
            .iter()
            .any(|d| matches!(d, Directive::Transaction(t) if t.flag == 'P')),
        "the fixture must actually synthesize a padding transaction, or this \
         test is comparing the unexpanded stream to itself",
    );
    assert_eq!(
        first_inversion(&expanded),
        None,
        "the pad-expanded stream must stay globally date-sorted (#1991)",
    );
}
