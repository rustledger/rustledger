//! The lossless round-trip assertions, shared by `fuzz_parse` and
//! `fuzz_green_eq_red` through `#[path]` so both corpora check the same
//! property.
//!
//! `parse_structured` documents "round-trip byte-identical for every UTF-8
//! input", and the lossless token stream must cover the input exactly once,
//! in order. Both were broken by column-0 `#` comments (#2769, #2775)
//! without any fuzz target noticing, because none asserted them.
//!
//! An org-mode heading (a column-0 `*` line) is ignored by beancount, so no
//! token that starts on one may run past the line's end (#2778). Before the
//! fix a `"` in the heading opened a string that swallowed the following
//! lines while staying lossless, so the round-trip check alone missed it.

use rustledger_parser::logos_lexer::{Token, tokenize_lossless};
use rustledger_parser::parse_structured;

pub fn assert_lossless(input: &str) {
    assert_eq!(
        parse_structured(input).text().to_string(),
        input,
        "parse_structured is not lossless"
    );

    let tokens = tokenize_lossless(input);
    let mut at = 0;
    for (_, span) in &tokens {
        assert_eq!(span.start, at, "lossless token stream has a gap or overlap");
        at = span.end;
    }
    assert_eq!(at, input.len(), "lossless token stream stops short");

    // An error token never spans a line ending: an unterminated `"` is
    // reported on its own line and lexing resumes on the next (#2784).
    // Before that fix it swallowed the rest of the file as one error.
    for (token, span) in &tokens {
        if matches!(token, Token::Error(_)) {
            assert!(
                !input[span.start..span.end].contains('\n'),
                "an error token runs past its line"
            );
        }
    }

    // A line is a heading when the lexer put a `Star` at its first byte after
    // any BOMs. Anchoring on the token (not on the text) keeps a line that
    // only LOOKS like one out, e.g. a `*` line inside a multi-line string.
    let star_starts: std::collections::HashSet<usize> = tokens
        .iter()
        .filter(|(t, _)| matches!(t, Token::Star))
        .map(|(_, s)| s.start)
        .collect();
    for (token, span) in &tokens {
        if matches!(token, Token::Newline) {
            continue;
        }
        let line_start = input[..span.start].rfind('\n').map_or(0, |i| i + 1);
        let line = &input[line_start..];
        let star_at = line_start + (line.len() - line.trim_start_matches('\u{FEFF}').len());
        if !star_starts.contains(&star_at) || span.start < star_at {
            continue;
        }
        let line_end = line.find('\n').map_or(input.len(), |i| line_start + i);
        assert!(
            span.end <= line_end,
            "a token on an org-mode heading line runs past the line end"
        );
    }
}
