//! Long tokens must not overflow the stack (#2789).
//!
//! logos's default codegen emits tail-calling state functions, and several of
//! the lexer's patterns recursed once per character or per repetition: escape
//! pairs and multi-byte characters inside strings, multi-byte text in
//! accounts and comments, account segments, and thousands groups in numbers.
//! A long enough token overflowed the stack in debug builds, and in release
//! wasm32 (no tail calls) at about 10 KB of `1,000,000,...` or
//! `Assets:B:B:...`. The workspace now enables logos's
//! `state_machine_codegen`, which emits one looping state machine.
//!
//! Each test lexes and parses one such shape on a thread with a 1 MB stack:
//! enough for the state machine's single large debug frame, far too little
//! for one frame per character. With the recursion back, the test's process
//! aborts (CI runs each test in its own process, so the failing shape is
//! named).

use rustledger_parser::logos_lexer::{Token, tokenize_lossless};
use rustledger_parser::parse;

const STACK: usize = 1024 * 1024;
const N: usize = 200_000;

/// Lex and parse `src` on a small-stack thread; return the token kinds'
/// debug names (first token only, to keep it cheap), the token count, and
/// the parse's (error count, directive count).
fn run(src: String) -> (String, usize, (usize, usize)) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let tokens = tokenize_lossless(&src);
            let first = tokens
                .first()
                .map(|(t, _)| format!("{t:?}").chars().take(20).collect())
                .unwrap_or_default();
            let r = parse(&src);
            (first, tokens.len(), (r.errors.len(), r.directives.len()))
        })
        .expect("spawn")
        .join()
        .expect("the thread did not panic")
}

#[test]
fn test_tokenize_lossless_string_of_escape_pairs_on_a_small_stack() {
    let src = format!("\"{}\"", "\\\"".repeat(N));
    let (first, count, _) = run(src);
    assert!(first.starts_with("String("), "{first}");
    assert_eq!(count, 1);
}

#[test]
fn test_tokenize_lossless_string_of_multibyte_chars_on_a_small_stack() {
    let src = format!("\"{}\"", "é".repeat(N));
    let (first, count, _) = run(src);
    assert!(first.starts_with("String("), "{first}");
    assert_eq!(count, 1);
}

/// The issue's reproducer: a stray quote, then escapes alternating with
/// line breaks. One error per line, nothing lost.
#[test]
fn test_parse_issue_2789_reproducer_on_a_small_stack() {
    let src = "\\\"\n".repeat(50_000) + "\\\n";
    let (_, count, (errors, directives)) = run(src);
    assert_eq!(count, 3 * 50_000 + 2);
    assert_eq!(directives, 0);
    assert!(errors > 0);
}

/// One `Number` token for the whole run of thousands groups (the value is
/// far too large for a decimal, which is the parser's business, not the
/// lexer's).
#[test]
fn test_tokenize_lossless_number_with_many_thousands_groups_on_a_small_stack() {
    let src = format!("1{}", ",000".repeat(N));
    let (first, count, _) = run(src);
    assert!(first.starts_with("Number("), "{first}");
    assert_eq!(count, 1);
}

#[test]
fn test_parse_account_with_many_segments_on_a_small_stack() {
    let src = format!("2024-01-01 open Assets{}\n", ":B".repeat(N));
    let (_, _, (errors, directives)) = run(src);
    assert_eq!((errors, directives), (0, 1));
}

/// One `Account` token for a segment that continues in multi-byte text.
#[test]
fn test_tokenize_lossless_account_with_long_multibyte_segment_on_a_small_stack() {
    let src = format!("Assets:B{}", "é".repeat(N));
    let (first, count, _) = run(src);
    assert!(first.starts_with("Account("), "{first}");
    assert_eq!(count, 1);
}

#[test]
fn test_parse_comments_with_multibyte_text_on_a_small_stack() {
    for prefix in [";", "%", "#!", "#+"] {
        let src = format!("{prefix}{}\n2024-01-01 open Assets:A\n", "aé".repeat(N));
        let (first, _, (errors, directives)) = run(src);
        assert!(
            !first.starts_with("Error("),
            "{prefix}: the comment lexed as {first}"
        );
        assert_eq!((errors, directives), (0, 1), "{prefix}");
    }
}

/// The token kinds above come from `Debug`; keep the type in use so the
/// import stays checked.
#[test]
fn test_token_debug_names_used_above_exist() {
    assert!(format!("{:?}", Token::String("\"\"")).starts_with("String("));
}
