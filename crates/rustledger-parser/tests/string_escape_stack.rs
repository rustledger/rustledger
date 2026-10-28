//! A long run of escapes inside a string must not overflow the stack
//! (#2789).
//!
//! logos compiled the string regex `"([^"\\]|\\.)*"` into mutually recursive
//! state functions, one stack frame per escape pair, so `"\"\"\"...` with
//! 50,000 pairs overflowed a 2 MB stack in a debug build, and could in any
//! build where the recursion is not turned into a loop (wasm32 has no tail
//! calls). The string is now scanned by a plain loop. These tests parse such
//! inputs on a thread with a deliberately small stack: with the recursion
//! back, the whole test process aborts.

use rustledger_parser::logos_lexer::{Token, tokenize_lossless};
use rustledger_parser::parse;

const SMALL_STACK: usize = 256 * 1024;
const PAIRS: usize = 200_000;

fn on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(SMALL_STACK)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("the thread did not panic")
}

/// A closed string full of escaped quotes is one `String` token.
#[test]
fn test_tokenize_lossless_long_escape_run_in_a_string_on_a_small_stack() {
    let src = format!("\"{}\"", "\\\"".repeat(PAIRS));
    let len = src.len();
    let tokens = on_small_stack(move || {
        tokenize_lossless(&src)
            .iter()
            .map(|(t, s)| (matches!(t, Token::String(_)), s.start, s.end))
            .collect::<Vec<_>>()
    });
    assert_eq!(tokens, [(true, 0, len)]);
}

/// The same run without a closing quote fails as one error to the end of the
/// input, and `parse` keeps the directive after it on its own line.
#[test]
fn test_parse_long_unterminated_escape_run_on_a_small_stack() {
    let src = format!("\"{}\n2024-01-02 open Assets:B\n", "\\\"".repeat(PAIRS));
    let result = on_small_stack(move || {
        let r = parse(&src);
        (r.errors.len(), r.directives.len())
    });
    assert_eq!(result, (1, 1));
}

/// A note whose description is a long escape run parses to that note.
#[test]
fn test_parse_note_with_long_escape_run_on_a_small_stack() {
    let src = format!(
        "2024-01-01 open Assets:A\n2024-01-02 note Assets:A \"{}\"\n",
        "\\\\".repeat(PAIRS)
    );
    let result = on_small_stack(move || {
        let r = parse(&src);
        (r.errors.len(), r.directives.len())
    });
    assert_eq!(result, (0, 2));
}
