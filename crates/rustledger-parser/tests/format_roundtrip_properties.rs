//! The formatter must never change what a file means: idempotence, meaning,
//! comments and errors, checked by one oracle (`format_roundtrip::check`,
//! shared with the `fuzz_format_roundtrip` fuzz target) over
//!
//! * every ledger in the repository's corpora (`tests/` at the workspace
//!   root, the `format_compat` fixtures, and every committed fuzz
//!   regression input);
//! * generated realistic ledgers (`format_roundtrip_common/ledger_gen.rs`);
//! * a minimized regression for each bug the properties found.
//!
//! The parser's fuzz corpus (the `fuzz-corpus` branch) is replayed through
//! the oracle by the `fuzz_format_roundtrip` target in `fuzz.yml`, which seeds
//! it from `fuzz_parse`'s corpus; `explore_dir` below runs the same sweep
//! locally over any directory.

use std::fs;
use std::path::{Path, PathBuf};

use proptest::prelude::*;
use rustledger_parser::format::{format_source, try_format_source};
use rustledger_parser::parse;

#[path = "../fuzz/fuzz_targets/common/format_roundtrip.rs"]
mod format_roundtrip;

#[path = "format_roundtrip_common/ledger_gen.rs"]
mod ledger_gen;

/// Every file under `dir`, recursively; with `exts`, only those extensions.
fn collect(dir: &Path, exts: &[&str], out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect(&p, exts, out);
        } else if exts.is_empty()
            || p.extension()
                .and_then(|x| x.to_str())
                .is_some_and(|x| exts.contains(&x))
        {
            out.push(p);
        }
    }
}

/// Run the oracle over `files`; returns how many were valid UTF-8 (and so
/// checked) and the failure reports.
fn sweep(files: &[PathBuf]) -> (usize, Vec<String>) {
    let mut failures = Vec::new();
    let mut checked = 0;
    for f in files {
        let Ok(bytes) = fs::read(f) else { continue };
        let Ok(src) = std::str::from_utf8(&bytes) else {
            continue;
        };
        checked += 1;
        match std::panic::catch_unwind(|| format_roundtrip::check(src)) {
            Ok(Ok(())) => {}
            Ok(Err(e)) => failures.push(format!("[{}] {e}", f.display())),
            Err(_) => failures.push(format!("[{}] panicked", f.display())),
        }
    }
    (checked, failures)
}

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Every ledger in the workspace's `tests/` tree (compatibility files,
/// regression fixtures, the lima tests, examples) and the `format_compat`
/// fixtures, clean and broken alike.
#[test]
fn test_format_roundtrip_on_repository_ledgers() {
    let root = manifest_dir().join("../..");
    let mut files = Vec::new();
    collect(
        &root.join("tests"),
        &["beancount", "bean", "txtpb"],
        &mut files,
    );
    collect(
        &manifest_dir().join("tests/format_compat/cases"),
        &["bean"],
        &mut files,
    );
    files.sort();
    let (checked, failures) = sweep(&files);
    // Fails loudly if the sweep silently stops finding the corpora.
    assert!(checked >= 500, "only {checked} ledgers checked");
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// Every committed fuzz regression input of every crate: the shapes that
/// already broke something once.
#[test]
fn test_format_roundtrip_on_fuzz_regressions() {
    let crates = manifest_dir().join("..");
    let mut files = Vec::new();
    for dir in fs::read_dir(&crates).expect("read crates/").flatten() {
        collect(&dir.path().join("fuzz/regressions"), &[], &mut files);
    }
    collect(
        &manifest_dir().join("tests/fuzz_regressions"),
        &[],
        &mut files,
    );
    files.retain(|f| f.extension().is_none_or(|x| x != "md"));
    files.sort();
    let (checked, failures) = sweep(&files);
    assert!(checked >= 8, "only {checked} regression inputs checked");
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// The sweep over any directory, for a local run over the parser fuzz corpus:
///
/// ```sh
/// git fetch --depth=1 origin fuzz-corpus
/// mkdir -p /tmp/corpus && git archive FETCH_HEAD fuzz_parse | tar -x -C /tmp/corpus
/// FORMAT_CORPUS_DIR=/tmp/corpus cargo test --release -p rustledger-parser \
///   --test format_roundtrip_properties explore_dir -- --ignored
/// ```
#[test]
#[ignore = "local corpus sweep: set FORMAT_CORPUS_DIR"]
fn explore_dir() {
    let dir = std::env::var("FORMAT_CORPUS_DIR").expect("set FORMAT_CORPUS_DIR");
    let mut files = Vec::new();
    collect(Path::new(&dir), &[], &mut files);
    files.sort();
    let (checked, failures) = sweep(&files);
    if let Ok(out) = std::env::var("FORMAT_CORPUS_OUT") {
        fs::write(out, failures.join("\n\n=====\n\n")).expect("write FORMAT_CORPUS_OUT");
    }
    assert!(
        failures.is_empty(),
        "{} of {checked} inputs failed; first:\n{}",
        failures.len(),
        failures[0]
    );
}

/// Proptest cases: `FORMAT_ROUNDTRIP_CASES`, else 256.
fn cases() -> u32 {
    std::env::var("FORMAT_ROUNDTRIP_CASES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(256)
}

/// Generated realistic ledgers keep their meaning, comments and cleanliness,
/// and format idempotently; the CLI's entry agrees.
#[test]
fn test_format_roundtrip_on_generated_ledgers() {
    ledger_gen::run_property(cases(), ledger_gen::ledger, |src| {
        let parsed = parse(&src);
        // The generator only writes clean ledgers; a generator bug must not
        // turn the property into a check of error recovery.
        prop_assert!(
            parsed.errors.is_empty(),
            "generator produced a broken ledger: {:?}\n{src:?}",
            parsed.errors
        );
        if let Err(e) = format_roundtrip::check(&src) {
            prop_assert!(false, "{}", e);
        }
        Ok(())
    });
}

// ---- Minimized regressions, one per root cause -------------------------

/// Assert the oracle passes on `src`.
fn assert_roundtrip(src: &str) {
    if let Err(e) = format_roundtrip::check(src) {
        panic!("{e}");
    }
}

/// A `\r` with more of the line after it, inside a comment, is comment text:
/// beancount's `;.*` takes it, and so does the lexer now. The formatter wrote
/// only the part before the `\r` (deleting `\rmore` from a trailing comment),
/// or, from `format_source`, folded the `\r` into a line break, which made the
/// rest of the comment a line of its own (here an open the comment had
/// hidden).
#[test]
fn test_format_source_keeps_a_bare_cr_in_a_comment() {
    for src in [
        "2024-01-01 open Assets:A ;c \rmore\n",
        "; c\r2024-01-01 open Assets:A\n",
        "#!\rqu\n",
        "#+b\rpo\n",
        "% x\ry\n",
    ] {
        assert!(parse(src).errors.is_empty(), "{src:?}");
        let out = format_source(src);
        assert_eq!(Ok(&out), try_format_source(src).as_ref(), "{src:?}");
        assert_roundtrip(src);
    }
    assert_eq!(
        format_source("2024-01-01 open Assets:A ;c \rmore\n"),
        "2024-01-01 open Assets:A ;c \rmore\n"
    );
    assert_eq!(
        format_source("; c\r2024-01-01 open Assets:A\n"),
        "; c\r2024-01-01 open Assets:A\n"
    );
}

/// A classic-Mac `\r`-only file is one broken line, to bean-check too
/// (`unexpected DATE`). `format_source` used to fold its `\r`s into line
/// breaks, turning it into a different, valid file.
#[test]
fn test_format_source_keeps_a_classic_mac_file_broken() {
    let src = "2024-01-01 open Assets:A\r2024-01-02 open Assets:B\r";
    assert!(!parse(&format_source(src)).errors.is_empty());
    assert_roundtrip(src);
}

/// A BOM after the leading one is text the parser keeps in the tree. The
/// formatter stripped the leading BOM and the parser then took the second for
/// the leading one, and the top-level walk skipped a BOM token, so each pass
/// dropped one more.
#[test]
fn test_format_source_keeps_a_second_bom() {
    for src in [
        "\u{FEFF}\u{FEFF}",
        "\u{FEFF}\u{FEFF}\u{FEFF}",
        "\u{FEFF}\u{FEFF}2229-2-3?",
        "\u{FEFF}\u{FEFF}\n\n<\n",
    ] {
        assert_roundtrip(src);
    }
    assert_eq!(format_source("\u{FEFF}\u{FEFF}"), "\u{FEFF}\u{FEFF}\n");
}

/// Unicode whitespace (a no-break space, a vertical tab) is an error to the
/// lexer. The verbatim copy of a broken line trimmed it with `str::trim_end`,
/// deleting the error with it.
#[test]
fn test_format_source_keeps_unicode_whitespace_errors() {
    for src in [
        "\u{a0}\n",
        "\u{b} \n",
        "\u{205f}\n",
        "2024-01-01 open Assets:A\n\u{a0}\u{a0}\n",
    ] {
        assert!(!parse(src).errors.is_empty(), "{src:?}");
        assert_roundtrip(src);
    }
}

/// Inside bison's recovery window after a failed line beancount reports no
/// syntax error, and the parser quiets its own to match, but the text there
/// is still unread. The formatter copies only directives holding an error
/// verbatim, so it rebuilt these from their typed values and deleted the
/// unread text: `include E` became `include`, and a `plugin` line's body
/// lines (`name: ...`) vanished.
#[test]
fn test_format_source_keeps_directives_with_quieted_errors() {
    let src = "includeX\nincludeE\n";
    assert_eq!(format_source(src), src);
    assert_roundtrip(src);
    let src = "info {\n  plugin {\n    name: \"beancount.plugin.unrealized\"\n  }\n}\n";
    assert_roundtrip(src);
    assert!(format_source(src).contains("name: \"beancount.plugin.unrealized\""));
}

/// A lone capital before a `\r` is beancount's invalid token (`CAPITAL`
/// needs a space, a tab or a `\n` after it): `open Assets:As,A\r\n` is an
/// error there, `open Assets:As,A\n` a valid open. Folding the CRLF, or
/// dropping a stray `\r` before the line ending, repaired the line, which the
/// formatter then rebuilt. A broken line now keeps its line ending.
#[test]
fn test_format_source_keeps_a_broken_lines_cr() {
    for src in [
        "2024-01-01 open Assets:As,A\r\n",
        "2024-01-01 open Assets:As,A\r\n2024-01-02 open Assets:B\r\n",
        "3132-7-7R\r\t\nt\n",
        "+4K\r",
    ] {
        assert!(!parse(src).errors.is_empty(), "{src:?}");
        assert!(!parse(&format_source(src)).errors.is_empty(), "{src:?}");
        assert_roundtrip(src);
    }
    assert_eq!(
        format_source("2024-01-01 open Assets:As,A\r\n2024-01-02 open   Assets:B\r\n"),
        "2024-01-01 open Assets:As,A\r\n2024-01-02 open Assets:B\n"
    );
}

/// A lone capital at the end of the file is an invalid token too, and before
/// a `\n` it is not: the final newline the formatter adds repaired a broken
/// last line, which the next pass rebuilt. A broken last line without a
/// newline keeps going without one. (After a failed line the parser reports
/// the `T` as beancount does; see the report for the clean-line case.)
#[test]
fn test_format_source_adds_no_newline_after_a_broken_last_line() {
    let src = "pushmeta\t\txn:Oxn:O\n0861-02-13T;:-3\n0861-02-13T";
    assert!(!parse(src).errors.is_empty());
    assert_eq!(format_source(src), src);
    assert_roundtrip(src);
    // A broken last line the newline does not repair still gets one.
    assert_eq!(format_source("pushtag"), "pushtag\n");
    // A clean last line still gets its newline.
    assert_eq!(
        format_source("2024-01-01 open Assets:A"),
        "2024-01-01 open Assets:A\n"
    );
}

/// `fuzz_format_roundtrip` crash (`fuzz/regressions/fuzz_format_roundtrip/
/// leading-indented-comment`): a file-leading indented comment was moved to
/// column 0. rledger reads such a comment as a comment on purpose (beancount
/// reports `unexpected INDENT` there) but keeps bison's recovery after it
/// quiet, so the indented line after it is clean; after a column-0 comment
/// it is an error, and formatting broke a clean file.
#[test]
fn test_format_source_keeps_a_leading_indented_comment_indented() {
    let src = "\t;\n\t+";
    assert!(parse(src).errors.is_empty());
    assert_eq!(format_source(src), "\t;\n\t+\n");
    assert_roundtrip(src);
}
