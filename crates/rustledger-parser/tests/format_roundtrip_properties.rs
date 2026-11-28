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

/// `fuzz_format_roundtrip` crash (#3084, `fuzz/regressions/
/// fuzz_format_roundtrip/crash-98ac0a55...`): after a second BOM, the
/// (former) line-ending fold found the string literals with the bare lexer, which
/// glues that BOM into an invalid token with the `"""` after it, so the `"`
/// on the next line opened a string holding the `\r\n`, and the fold left it.
/// The tree the formatter emits makes the BOM a token of its own and reads
/// `""` and `"\n"` there, the `\r\n` a line ending outside any string, which
/// the verbatim copy of its error node kept with one more blank line ahead of
/// it on every pass. #3085 made the fold read strings as the tree does;
/// the fold is gone now (ADR 0009 phase B): the `\r\n` there is a blank line
/// between two regions copied as written, which the formatter writes as
/// `\n`, and one inside a string the tree reads is the string's. The broken
/// last line gets no newline.
#[test]
fn test_format_source_reads_line_endings_as_the_tree_reads_a_second_bom() {
    let src = "\u{FEFF}\u{FEFF}\"\"\"\n\"\n\r\n\"";
    assert_eq!(format_source(src), "\u{FEFF}\u{FEFF}\"\"\"\n\"\n\n\"");
    assert_roundtrip(src);
    let src = "\u{FEFF}\u{FEFF}\"\n\r\n\"";
    assert_eq!(format_source(src), src);
    assert_roundtrip(src);
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
/// last line, which the next pass rebuilt. A broken last line is copied as
/// written, so it keeps going without one. (After a failed line the parser
/// reports the `T` as beancount does; see the report for the clean-line case.)
#[test]
fn test_format_source_adds_no_newline_after_a_broken_last_line() {
    let src = "pushmeta\t\txn:Oxn:O\n0861-02-13T;:-3\n0861-02-13T";
    assert!(!parse(src).errors.is_empty());
    assert_eq!(format_source(src), src);
    assert_roundtrip(src);
    // So does every broken last line (ADR 0009 phase B: the formatter adds
    // no text to a line it does not own).
    assert_eq!(format_source("pushtag"), "pushtag");
    // A clean last line still gets its newline.
    assert_eq!(
        format_source("2024-01-01 open Assets:A"),
        "2024-01-01 open Assets:A\n"
    );
}

/// `fuzz_format_roundtrip` crash (`fuzz/regressions/fuzz_format_roundtrip/
/// leading-indented-comment`): a file-leading indented comment was moved to
/// column 0. rledger reads such a comment as a comment on purpose (beancount
/// reports `unexpected INDENT` there), and the indented line after it is an
/// orphan to rledger, inside the recovery beancount starts at that indent:
/// one error, as for `  ; c` then `  !` (a parse rledger finds an error in
/// never comes out clean; `bison_recovery_model`). Formatting keeps the
/// comment indented, as after a column-0 comment it would read differently.
#[test]
fn test_format_source_keeps_a_leading_indented_comment_indented() {
    let src = "\t;\n\t+";
    assert_eq!(parse(src).errors.len(), 1);
    // The broken last line is copied as written, without a newline.
    assert_eq!(format_source(src), src);
    assert_roundtrip(src);
}

// ---- Exhaustive short inputs ---------------------------------------------

/// The symbols the exhaustive sweep strings together: the bytes every
/// line-ending, BOM and string-literal frame bug so far was made of, plus a
/// date to make the rest a directive.
const SYMBOLS: [&str; 10] = [
    "\u{FEFF}",
    "\"",
    "\n",
    "\r",
    "\r\n",
    "A",
    ";",
    "*",
    " ",
    "2024-01-01 ",
];

/// Every string of at most `depth` symbols.
fn short_inputs(depth: u32) -> Vec<String> {
    let mut all = vec![String::new()];
    let mut layer = vec![String::new()];
    for _ in 0..depth {
        layer = layer
            .iter()
            .flat_map(|s| SYMBOLS.iter().map(move |sym| format!("{s}{sym}")))
            .collect();
        all.extend(layer.iter().cloned());
    }
    all
}

/// The inputs of the default sweep the certifier has to demote, one `Debug`
/// literal per line: emitter bugs the certifier keeps from users, pinned so
/// the list can only shrink (each fix removes its lines; a new demotion is a
/// new emitter bug and fails here).
const DEMOTIONS_MANIFEST: &str = "tests/format_roundtrip_common/exhaustive_demotions.manifest";

/// Exhaustive sweep depth: `FORMAT_EXHAUSTIVE_DEPTH`, else 4 (11,111 inputs).
/// The manifest is for the default depth; at another depth the sweep checks
/// the promises and only reports demotions.
const DEFAULT_DEPTH: u32 = 4;

/// Every string of up to four symbols keeps every promise (the certifier makes
/// sure of that), and the ones it has to demote to do so are exactly those in
/// the manifest: a demotion ratchet. Regenerate with
/// `FORMAT_DEMOTIONS_UPDATE=1`.
#[test]
fn test_format_exhaustive_short_inputs() {
    let depth = std::env::var("FORMAT_EXHAUSTIVE_DEPTH")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_DEPTH);
    let mut failures = Vec::new();
    let mut demoted = Vec::new();
    for src in short_inputs(depth) {
        if let Err(e) = format_roundtrip::check_promises(&src) {
            failures.push(e);
        }
        let (_, report) = rustledger_parser::format::__format_source_report(
            &src,
            rustledger_parser::format::GroupingStyle::default(),
        );
        if !report.is_clean() {
            demoted.push(format!("{src:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} inputs broke a promise; first:\n{}",
        failures.len(),
        failures[0]
    );
    if depth != DEFAULT_DEPTH {
        eprintln!("{} inputs demoted:\n{}", demoted.len(), demoted.join("\n"));
        return;
    }
    let path = manifest_dir().join(DEMOTIONS_MANIFEST);
    let header = "# Inputs of `test_format_exhaustive_short_inputs` the formatter's certifier\n\
                  # demotes (ADR 0009): emitter bugs it keeps from users. May only shrink.\n\
                  # Regenerate: FORMAT_DEMOTIONS_UPDATE=1 cargo test -p rustledger-parser \\\n\
                  #   --test format_roundtrip_properties test_format_exhaustive_short_inputs\n";
    let body: String = demoted.iter().flat_map(|d| [d.as_str(), "\n"]).collect();
    if std::env::var_os("FORMAT_DEMOTIONS_UPDATE").is_some() {
        fs::write(&path, format!("{header}{body}")).expect("write the manifest");
        return;
    }
    let pinned: Vec<&str> = include_str!("format_roundtrip_common/exhaustive_demotions.manifest")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .collect();
    let new: Vec<&String> = demoted
        .iter()
        .filter(|d| !pinned.contains(&d.as_str()))
        .collect();
    let fixed: Vec<&&str> = pinned
        .iter()
        .filter(|p| !demoted.iter().any(|d| d == **p))
        .collect();
    assert!(
        new.is_empty() && fixed.is_empty(),
        "the certifier's demotions changed (regenerate {DEMOTIONS_MANIFEST} with \
         FORMAT_DEMOTIONS_UPDATE=1 once intended)\nnewly demoted: {new:#?}\nno longer demoted: {fixed:#?}"
    );
}
