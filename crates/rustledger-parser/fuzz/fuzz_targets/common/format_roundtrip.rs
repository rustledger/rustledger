//! The formatter round-trip oracle: `format_source` must never change what a
//! file means.
//!
//! Shared through `#[path]` by the `fuzz_format_roundtrip` fuzz target and the
//! parser's `format_roundtrip_properties` test, so the fuzz corpus, the
//! proptest generator and the on-disk corpora all check one definition.
//!
//! [`check`] asserts, for ANY UTF-8 input:
//!
//! 1. **Idempotence.** `format(format(x)) == format(x)`.
//! 2. **Meaning.** The directives, options, includes and plugins parsed from
//!    the output equal those parsed from the input. Compared through `Debug`
//!    with spans stripped, not `PartialEq`, because `Decimal`'s equality
//!    ignores scale (`1.5 == 1.50`) while the scale is meaning in beancount
//!    (display precision, tolerance inference).
//!    Comment values are compared without their trailing blanks, which the
//!    canonical form trims. On a broken file, directives touching an error
//!    line are left out (recovery artifacts; the lines themselves are kept
//!    verbatim, see 4).
//! 3. **Comments.** The same comments, with the same text, in the same slot:
//!    see [`comment_stream`]. (On a broken file, the same comments in the
//!    same order; the slots there come from error recovery.)
//! 4. **Errors.** A clean file stays clean and a broken one stays broken:
//!    every line holding a parse error is kept byte for byte, and a line
//!    gains a reported error only where the input already held a quieted
//!    one (see `check`). `try_format_source` (the CLI's entry) refuses
//!    exactly the inputs with errors, and otherwise agrees with
//!    `format_source` byte for byte.

use rustledger_parser::format::{format_source, try_format_source};
use rustledger_parser::{NodeOrToken, ParseResult, SyntaxKind, WalkEvent, parse};

/// `Debug` text with every `span: Span { start: N, end: N }` removed, so two
/// values that differ only in where they sit in the file compare equal while
/// every other field, decimal scale included, still counts.
pub fn strip_spans(debug: &str) -> String {
    const OPEN: &str = "span: Span { start: ";
    let mut out = String::with_capacity(debug.len());
    let mut rest = debug;
    while let Some(i) = rest.find(OPEN) {
        out.push_str(&rest[..i]);
        let after = &rest[i..];
        let end = after.find('}').map_or(after.len(), |j| j + 1);
        rest = &after[end..];
    }
    out.push_str(rest);
    out
}

/// `debug` with the trailing blanks of every comment string inside a
/// `CommentList(...)` removed. A comment's value keeps the blanks after its
/// text, and the canonical form trims trailing whitespace; that is a
/// whitespace change, not a change of meaning.
fn trim_comment_blanks(debug: &str) -> String {
    const OPEN: &str = "CommentList(Some([";
    let mut out = String::with_capacity(debug.len());
    let mut rest = debug;
    while let Some(i) = rest.find(OPEN) {
        out.push_str(&rest[..i + OPEN.len()]);
        rest = &rest[i + OPEN.len()..];
        // Walk the list's string literals (Debug-escaped) up to its `]`.
        let mut chars = rest.char_indices();
        let mut in_string = false;
        let mut end = rest.len();
        while let Some((j, c)) = chars.next() {
            match c {
                '\\' if in_string => {
                    out.push(c);
                    if let Some((_, e)) = chars.next() {
                        out.push(e);
                    }
                    continue;
                }
                '"' if in_string => {
                    loop {
                        if out.ends_with(' ') {
                            out.pop();
                        } else if out.ends_with("\\t") {
                            out.truncate(out.len() - 2);
                        } else {
                            break;
                        }
                    }
                    in_string = false;
                }
                '"' => in_string = true,
                ']' if !in_string => {
                    end = j;
                    break;
                }
                _ => {}
            }
            out.push(c);
        }
        rest = &rest[end..];
    }
    out.push_str(rest);
    out
}

/// Everything a parse of `src` yields that carries meaning, spans dropped,
/// leaving out what touches a line in `skip` (0-based).
pub fn meaning(src: &str, r: &ParseResult, skip: &[usize]) -> Vec<String> {
    let lines_of = |span: rustledger_parser::Span| {
        let line = |at: usize| newlines_before(src, at);
        let (a, b) = (
            line(span.start),
            line(span.end.saturating_sub(1).max(span.start)),
        );
        !skip.iter().any(|l| (a..=b).contains(l))
    };
    let mut out: Vec<String> = r
        .directives
        .iter()
        .filter(|d| lines_of(d.span))
        .map(|d| trim_comment_blanks(&strip_spans(&format!("{:?}", d.value))))
        .collect();
    out.extend(
        r.options
            .iter()
            .filter(|(_, _, s)| lines_of(*s))
            .map(|(k, v, _)| format!("option {k:?} {v:?}")),
    );
    out.extend(
        r.includes
            .iter()
            .filter(|(_, s)| lines_of(*s))
            .map(|(p, _)| format!("include {p:?}")),
    );
    out.extend(
        r.plugins
            .iter()
            .filter(|(_, _, s)| lines_of(*s))
            .map(|(n, c, _)| format!("plugin {n:?} {c:?}")),
    );
    out
}

/// The 0-based lines of `src` that hold a parse error of `r`.
fn error_line_numbers(src: &str, r: &ParseResult) -> Vec<usize> {
    r.errors
        .iter()
        .map(|e| newlines_before(src, e.span.start))
        .collect()
}

/// The text of the line holding byte `at` of `src`, right-trimmed.
fn line_at(src: &str, at: usize) -> &str {
    let at = at.min(src.len());
    let at = (0..=at)
        .rev()
        .find(|&i| src.is_char_boundary(i))
        .unwrap_or(0);
    let start = src[..at].rfind('\n').map_or(0, |i| i + 1);
    let end = src[at..].find('\n').map_or(src.len(), |i| at + i);
    let line = src[start..end].trim_end_matches([' ', '\t', '\r']);
    // The file's leading BOM is not part of its first line (the formatter
    // drops it).
    if start == 0 {
        line.strip_prefix('\u{FEFF}').unwrap_or(line)
    } else {
        line
    }
}

/// The text of each line holding a parse error, in order, each once.
///
/// Lines, not messages: the formatter must keep every broken line broken and
/// byte-for-byte, but how many errors the parser reports on such a line may
/// depend on trivia the formatter drops. A stray `\r` before the line
/// ending is the one known case: `K\r` makes a lone capital beancount's
/// invalid token, one error more on a line that has one already.
pub fn error_lines(src: &str, r: &ParseResult) -> Vec<String> {
    let mut lines: Vec<String> = Vec::new();
    let mut last_start = None;
    for e in &r.errors {
        let at = e.span.start.min(src.len());
        let at = (0..=at)
            .rev()
            .find(|&i| src.is_char_boundary(i))
            .unwrap_or(0);
        let start = src[..at].rfind('\n').map_or(0, |i| i + 1);
        if last_start != Some(start) {
            last_start = Some(start);
            lines.push(format!("{:?}", line_at(src, at)));
        }
    }
    lines
}

/// The text of each line holding one of the byte offsets `at`, in order,
/// each once (as [`error_lines`] gives them).
fn lines_of_spans(src: &str, at: impl Iterator<Item = usize>) -> Vec<String> {
    let mut starts: Vec<usize> = at
        .map(|a| {
            let a = a.min(src.len());
            let a = (0..=a)
                .rev()
                .find(|&i| src.is_char_boundary(i))
                .unwrap_or(0);
            src[..a].rfind('\n').map_or(0, |i| i + 1)
        })
        .collect();
    starts.sort_unstable();
    starts.dedup();
    starts
        .into_iter()
        .map(|s| format!("{:?}", line_at(src, s)))
        .collect()
}

const fn is_comment(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::COMMENT
            | SyntaxKind::PERCENT_COMMENT
            | SyntaxKind::SHEBANG
            | SyntaxKind::EMACS_DIRECTIVE
    )
}

const fn is_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::WHITESPACE | SyntaxKind::NEWLINE | SyntaxKind::BOM
    ) || is_comment(kind)
}

/// The comments of a file, in order, interleaved with the structure they sit
/// in: `D` where a top-level directive starts, `E` an unparsable region, `P` a
/// posting, `M` a metadata line, and `C` a comment, marked trailing when text
/// precedes it on its line.
///
/// Markers are placed at a node's first non-trivia token rather than where the
/// node starts, so which node the CST hangs a comment's trivia on (leading
/// trivia of the next directive, trailing trivia of the last) does not matter:
/// only the comment's place in the source does. A comment that moves from one
/// posting to the next, from inside a string to after it, or from a header to
/// the body changes the stream.
pub fn comment_stream(src: &str, r: &ParseResult) -> Vec<String> {
    let root = r.syntax_node();
    // The CST is in post-BOM coordinates.
    let base = if r.has_leading_bom { 3 } else { 0 };
    let mut out = Vec::new();
    let mut pending: Vec<&'static str> = Vec::new();
    for event in root.preorder_with_tokens() {
        match event {
            WalkEvent::Enter(NodeOrToken::Node(n)) => {
                let top = n
                    .parent()
                    .is_some_and(|p| p.kind() == SyntaxKind::SOURCE_FILE);
                match n.kind() {
                    SyntaxKind::ERROR_NODE => pending.push("E"),
                    _ if top => pending.push("D"),
                    SyntaxKind::POSTING => pending.push("P"),
                    SyntaxKind::META_ENTRY => pending.push("M"),
                    _ => {}
                }
            }
            WalkEvent::Leave(NodeOrToken::Node(_)) => {}
            WalkEvent::Enter(NodeOrToken::Token(t)) => {
                let kind = t.kind();
                if is_comment(kind) {
                    let start = usize::from(t.text_range().start()) + base;
                    let before = &src[..start.min(src.len())];
                    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
                    let lead = before[line_start..].trim_start_matches('\u{FEFF}');
                    let trailing = !lead.trim().is_empty();
                    out.push(format!(
                        "C{} {:?}",
                        if trailing { "t" } else { "" },
                        t.text().trim_end_matches([' ', '\t', '\r'])
                    ));
                } else if !is_trivia(kind) {
                    out.extend(std::mem::take(&mut pending).into_iter().map(str::to_string));
                }
            }
            WalkEvent::Leave(NodeOrToken::Token(_)) => {}
        }
    }
    out.extend(pending.into_iter().map(str::to_string));
    out
}

/// Check every property on `src`. `Err` carries a report naming the property
/// that failed, the input and the output.
pub fn check(src: &str) -> Result<(), String> {
    let once = format_source(src);
    let report = |what: &str, detail: String| {
        Err(format!(
            "{what}\n--- input ---\n{src:?}\n--- formatted ---\n{once:?}\n{detail}"
        ))
    };

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
    let defect_lines = lines_of_spans(
        src,
        before
            .errors
            .iter()
            .map(|e| e.span.start)
            .chain(before.__defect_spans().iter().map(|s| s.start)),
    );
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
    let (m_before, m_after) = (
        meaning(src, &before, &error_line_numbers(src, &before)),
        meaning(&once, &after, &error_line_numbers(&once, &after)),
    );
    if m_before != m_after {
        let first = m_before
            .iter()
            .zip(&m_after)
            .position(|(a, b)| a != b)
            .unwrap_or(m_before.len().min(m_after.len()));
        return report(
            "meaning changed",
            format!(
                "{} vs {} items; first difference at {first}\n--- before ---\n{}\n--- after ---\n{}",
                m_before.len(),
                m_after.len(),
                m_before.get(first).map_or("<none>", String::as_str),
                m_after.get(first).map_or("<none>", String::as_str),
            ),
        );
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
