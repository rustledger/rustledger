//! The formatter round-trip oracle: `format_source` must never change what a
//! file means.
//!
//! Shared through `#[path]` by the `fuzz_format_roundtrip` fuzz target and the
//! parser's `format_roundtrip_properties` test, so the fuzz corpus, the
//! proptest generator and the on-disk corpora all check one definition.
//!
//! The definitions of "the same meaning" are the formatter's own
//! (`rustledger_parser::format::{__same_meaning, __comment_stream,
//! __error_lines, __defect_lines}`, in `cst/certify.rs`): the formatter
//! certifies every output item by item with them (ADR 0009), and this oracle
//! checks whole files with them, so the product and its tests cannot drift.
//!
//! [`check`] asserts, for ANY UTF-8 input:
//!
//! 0. **No demotion.** The certifier kept nothing verbatim that the emitter
//!    should have formatted: the canonical emitter alone already keeps every
//!    property below. Stricter than what users get (the certifier would have
//!    kept such an item as written), so an emitter bug still fails here.
//! 1. **Idempotence.** `format(format(x)) == format(x)`.
//! 2. **Meaning.** The directives, options, includes and plugins parsed from
//!    the output equal those parsed from the input, decimal scale and
//!    metadata order included (`same_directive`). Comment values are compared
//!    without their trailing blanks, which the canonical form trims. On a
//!    broken file, directives touching an error line are left out (recovery
//!    artifacts; the lines themselves are kept verbatim, see 4).
//! 3. **Comments.** The same comments, with the same text, in the same slot:
//!    see `__comment_stream`. (On a broken file, the same comments in the
//!    same order; the slots there come from error recovery.)
//! 4. **Errors.** A clean file stays clean and a broken one stays broken:
//!    every line holding a parse error is kept byte for byte, and a line
//!    gains a reported error only where the input already held a quieted
//!    one (see `check`). `try_format_source` (the CLI's entry) refuses
//!    exactly the inputs with errors, and otherwise agrees with
//!    `format_source` byte for byte.

use rustledger_parser::format::{
    __comment_stream, __defect_lines, __error_lines, __format_source_report, __same_meaning,
    GroupingStyle, format_source, try_format_source,
};
use rustledger_parser::{ParseResult, parse};

/// The text of each line holding a parse error, in order, each once.
///
/// Lines, not messages: the formatter must keep every broken line broken and
/// byte-for-byte, but how many errors the parser reports on such a line may
/// depend on trivia the formatter drops. A stray `\r` before the line
/// ending is the one known case: `K\r` makes a lone capital beancount's
/// invalid token, one error more on a line that has one already.
pub fn error_lines(src: &str, r: &ParseResult) -> Vec<String> {
    __error_lines(src, r)
}

/// The comments of a file, in order, interleaved with the structure they sit
/// in: `D` where a top-level directive starts, `E` an unparsable region, `P` a
/// posting, `M` a metadata line, and `C` a comment, marked trailing when text
/// precedes it on its line. The formatter's own definition (see the module
/// docs).
pub fn comment_stream(src: &str, r: &ParseResult) -> Vec<String> {
    __comment_stream(src, r)
}

/// The 0-based lines of `src` that hold a parse error of `r`.
fn error_line_numbers(src: &str, r: &ParseResult) -> Vec<usize> {
    r.errors
        .iter()
        .map(|e| newlines_before(src, e.span.start))
        .collect()
}

/// Check every property on `src`, no demotion included. `Err` carries a
/// report naming the property that failed, the input and the output.
pub fn check(src: &str) -> Result<(), String> {
    check_with(src, true)
}

/// Check the promises users get on `src`: every property but 0. The
/// certifier must make these hold on ANY input, demoting what it must.
pub fn check_promises(src: &str) -> Result<(), String> {
    check_with(src, false)
}

fn check_with(src: &str, no_demotion: bool) -> Result<(), String> {
    let (once, certified) = __format_source_report(src, GroupingStyle::default());
    let report = |what: &str, detail: String| {
        Err(format!(
            "{what}\n--- input ---\n{src:?}\n--- formatted ---\n{once:?}\n{detail}"
        ))
    };
    if no_demotion && !certified.is_clean() {
        return report(
            "the certifier had to keep part of the input as written (an emitter bug)",
            format!("{certified:?}"),
        );
    }
    if format_source(src) != once {
        return report("format_source disagrees with its report", String::new());
    }

    let twice = format_source(&once);
    if twice != once {
        return report(
            "not idempotent",
            format!("--- formatted twice ---\n{twice:?}"),
        );
    }

    let before = parse(src);
    let after = parse(&once);

    if before.errors.is_empty() != after.errors.is_empty() {
        return report(
            "a clean file became broken, or a broken one clean",
            format!(
                "--- before ---\n{:?}\n--- after ---\n{:?}",
                before.errors, after.errors
            ),
        );
    }
    // Every line holding an error is kept byte for byte, and no line gains
    // one. Equality of the reported lines is too strong: inside bison's
    // recovery window after a failed line, beancount (and so the parser)
    // reports only lexer errors, and whether a following broken line is
    // reported can turn on what the formatter normalizes: the final newline
    // it adds (`\nO\nO` is two error lines, `\nO\nO\n` one, as the newline
    // counts as one of bison's three shifts), or a `\r` folded or dropped
    // after a lone capital (`B\r` is beancount's invalid token, a lexer error
    // reported anywhere; `B` is a token the recovery discards in silence).
    // Such a line is broken before and after, and kept verbatim.
    let e_before = error_lines(src, &before);
    let e_after = error_lines(&once, &after);
    // A line may gain a reported error only where the input already held a
    // quieted one (`__defect_spans`): text inside bison's recovery window,
    // unread before and after, whose error the window hid.
    let defect_lines = __defect_lines(src, &before);
    if !is_subsequence(&e_after, &defect_lines) {
        return report(
            "a line gained a parse error",
            format!("--- before ---\n{e_before:#?}\n--- after ---\n{e_after:#?}"),
        );
    }
    let out_lines: Vec<String> = once
        .split('\n')
        .enumerate()
        .map(|(i, l)| {
            let l = l.trim_end_matches([' ', '\t', '\r']);
            let l = if i == 0 {
                l.strip_prefix('\u{FEFF}').unwrap_or(l)
            } else {
                l
            };
            format!("{l:?}")
        })
        .collect();
    if !is_subsequence(&e_before, &out_lines) {
        return report(
            "a line holding a parse error was not kept verbatim",
            format!("--- error lines ---\n{e_before:#?}"),
        );
    }

    match try_format_source(src) {
        Ok(cli) if !before.errors.is_empty() => {
            return report("try_format_source accepted a broken file", cli);
        }
        Ok(cli) if cli != once => {
            return report(
                "try_format_source disagrees with format_source",
                format!("--- try_format_source ---\n{cli:?}"),
            );
        }
        Err(_) if before.errors.is_empty() => {
            return report("try_format_source refused a clean file", String::new());
        }
        _ => {}
    }

    // On a broken file, a directive that touches an error line is a
    // recovery artifact: which values the parser salvages from a line it
    // cannot read depends on details the formatter is allowed to normalize
    // (the blanks trimmed from a broken line). Such lines are kept verbatim
    // (checked above); every other directive must keep its meaning exactly.
    if let Err(detail) = __same_meaning(
        (src, &before, &error_line_numbers(src, &before)),
        (&once, &after, &error_line_numbers(&once, &after)),
    ) {
        return report("meaning changed", detail);
    }

    let (mut c_before, mut c_after) = (comment_stream(src, &before), comment_stream(&once, &after));
    // On a broken file the structure markers come from error recovery, which
    // the formatter's normalization of a broken region (a whitespace-only line
    // trimmed to an empty one, which ends the region) may reshape; the
    // comments themselves, in order, must still all be there.
    if !before.errors.is_empty() {
        c_before.retain(|c| c.starts_with('C'));
        c_after.retain(|c| c.starts_with('C'));
    }
    if c_before != c_after {
        return report(
            "comments changed",
            format!("--- before ---\n{c_before:?}\n--- after ---\n{c_after:?}"),
        );
    }
    Ok(())
}

/// Whether `needle` is `hay` with some items left out, order kept.
fn is_subsequence(needle: &[String], hay: &[String]) -> bool {
    let mut hay = hay.iter();
    needle.iter().all(|n| hay.any(|h| h == n))
}

/// How many `\n`s `src` holds before byte `at`.
fn newlines_before(src: &str, at: usize) -> usize {
    let at = at.min(src.len());
    let at = (0..=at)
        .rev()
        .find(|&i| src.is_char_boundary(i))
        .unwrap_or(0);
    src[..at].matches('\n').count()
}
