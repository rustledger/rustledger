//! Drift guard: `format_source` must never change what a file means.
//!
//! The formatter rebuilds every directive from the CST, so a bug in it can
//! change a parsed value while every other check stays green. #3046 is the
//! example: a same-line trailing comment after a multi-line string was spliced
//! before the first `\n` of the emitted directive, which is inside the string,
//! so the comment became part of the narration (or query, custom value, note,
//! ...). The output parsed cleanly, was idempotent, and still held the comment
//! text, so neither the idempotence checks nor
//! `scripts/format-preserves-comments.sh` saw it.
//!
//! These tests compare the parsed directives (and options, includes and
//! plugins) of the input with those of the formatted output. `Spanned`'s
//! equality ignores spans, so only the values are compared.

use std::fs;
use std::path::Path;

use proptest::prelude::*;
use rustledger_parser::format::format_source;
use rustledger_parser::{ParseResult, parse};

/// Everything in a parse result that carries meaning, with spans dropped.
#[derive(Debug, PartialEq)]
struct Meaning {
    directives: Vec<rustledger_core::Directive>,
    options: Vec<(String, String)>,
    includes: Vec<String>,
    plugins: Vec<(String, Option<String>)>,
}

fn meaning(r: &ParseResult) -> Meaning {
    Meaning {
        directives: r.directives.iter().map(|d| d.value.clone()).collect(),
        options: r
            .options
            .iter()
            .map(|(k, v, _)| (k.clone(), v.clone()))
            .collect(),
        includes: r.includes.iter().map(|(p, _)| p.clone()).collect(),
        plugins: r
            .plugins
            .iter()
            .map(|(n, c, _)| (n.clone(), c.clone()))
            .collect(),
    }
}

/// Format `src`, then assert the output means what `src` means, parses
/// without errors, and is a fixed point of the formatter.
fn assert_format_preserves_meaning(name: &str, src: &str) -> Result<(), String> {
    let before = parse(src);
    if !before.errors.is_empty() {
        return Err(format!(
            "[{name}] input does not parse cleanly: {:?}\n{src:?}",
            before.errors
        ));
    }
    let formatted = format_source(src);
    let after = parse(&formatted);
    if !after.errors.is_empty() {
        return Err(format!(
            "[{name}] formatted output does not parse cleanly: {:?}\n--- input ---\n{src}\n--- output ---\n{formatted}",
            after.errors
        ));
    }
    let (m_before, m_after) = (meaning(&before), meaning(&after));
    if m_before != m_after {
        return Err(format!(
            "[{name}] formatting changed the parsed directives\n--- input ---\n{src}\n--- output ---\n{formatted}\n--- before ---\n{m_before:#?}\n--- after ---\n{m_after:#?}"
        ));
    }
    let twice = format_source(&formatted);
    if twice != formatted {
        return Err(format!(
            "[{name}] formatting is not idempotent\n--- once ---\n{formatted}\n--- twice ---\n{twice}"
        ));
    }
    Ok(())
}

/// Every `format_compat` fixture whose input parses cleanly keeps its meaning.
#[test]
fn test_format_source_preserves_directives_on_format_compat_fixtures() {
    let cases = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/format_compat/cases");
    let mut checked = 0;
    let mut failures = Vec::new();
    let mut dirs: Vec<_> = fs::read_dir(&cases)
        .unwrap_or_else(|e| panic!("read_dir({}): {e}", cases.display()))
        .map(|e| e.expect("read_dir entry").path())
        .collect();
    dirs.sort();
    for dir in dirs {
        let input = dir.join("input.bean");
        let Ok(src) = fs::read_to_string(&input) else {
            continue;
        };
        // A fixture with parse errors pins the error-tolerant path, which
        // copies the broken directive verbatim; there is no parsed meaning
        // to compare.
        if !parse(&src).errors.is_empty() {
            continue;
        }
        checked += 1;
        let name = dir.file_name().unwrap().to_string_lossy().into_owned();
        if let Err(e) = assert_format_preserves_meaning(&name, &src) {
            failures.push(e);
        }
    }
    // Fails loudly if the sweep silently stops seeing the fixtures.
    assert!(checked >= 30, "only {checked} fixtures checked");
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// Directive shapes with a string slot (`{S}`) on the line a same-line
/// trailing comment (`{C}`) ends. Every string the grammar allows on a
/// header, metadata or posting line is here (#3046).
const TEMPLATES: &[(&str, &str)] = &[
    (
        "narration",
        "2020-01-01 open Assets:A EUR\n2020-01-02 * \"{S}\"{C}\n  Assets:A  1 EUR\n  Assets:A  -1 EUR\n",
    ),
    (
        "payee",
        "2020-01-01 open Assets:A EUR\n2020-01-02 ! \"{S}\" \"n\"{C}\n  Assets:A  1 EUR\n  Assets:A  -1 EUR\n",
    ),
    (
        "narration_with_tags",
        "2020-01-02 * \"p\" \"{S}\" #t ^l{C}\n  Assets:A  1 EUR\n  Assets:A  -1 EUR\n",
    ),
    ("query_name", "2020-01-01 query \"{S}\" \"SELECT 1\"{C}\n"),
    ("query_string", "2020-01-01 query \"q\" \"{S}\"{C}\n"),
    ("custom_name", "2020-01-01 custom \"{S}\" 1 TRUE{C}\n"),
    ("custom_value", "2020-01-01 custom \"c\" \"{S}\"{C}\n"),
    (
        "note",
        "2020-01-01 open Assets:A\n2020-01-02 note Assets:A \"{S}\"{C}\n",
    ),
    ("event_type", "2020-01-01 event \"{S}\" \"d\"{C}\n"),
    ("event_description", "2020-01-01 event \"t\" \"{S}\"{C}\n"),
    (
        "document",
        "2020-01-01 open Assets:A\n2020-01-02 document Assets:A \"{S}\"{C}\n",
    ),
    ("option", "option \"title\" \"{S}\"{C}\n"),
    ("plugin_config", "plugin \"p\" \"{S}\"{C}\n"),
    ("include", "include \"{S}\"{C}\n"),
    (
        "directive_meta",
        "2020-01-01 open Assets:A\n  key: \"{S}\"{C}\n",
    ),
    (
        "transaction_meta",
        "2020-01-02 * \"x\"\n  key: \"{S}\"{C}\n  Assets:A  1 EUR\n  Assets:A  -1 EUR\n",
    ),
    (
        "posting_meta",
        "2020-01-02 * \"x\"\n  Assets:A  1 EUR\n    key: \"{S}\"{C}\n  Assets:A  -1 EUR\n",
    ),
    (
        "cost_label",
        "2020-01-02 * \"x\"\n  Assets:A  1 HOOL {10 EUR, \"{S}\"}{C}\n  Assets:A  -10 EUR\n",
    ),
];

const COMMENTS: &[&str] = &["", " ; note", "  ; note \"quoted\"", "\t;"];

/// Every template, filled with a two-line string, keeps its meaning. A fixed
/// sweep so the #3046 shapes are covered whatever proptest happens to draw.
#[test]
fn test_format_source_preserves_multiline_strings_with_trailing_comment() {
    let mut failures = Vec::new();
    for (name, template) in TEMPLATES {
        for comment in COMMENTS {
            for s in ["multi\nline", "a\n\nb", "x ; y\nz", "\n", "a\n  ; c\nb"] {
                let src = template.replace("{S}", s).replace("{C}", comment);
                if let Err(e) = assert_format_preserves_meaning(name, &src) {
                    failures.push(e);
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

proptest! {
    /// Any string body (newlines, `;`, spaces and `#` included) in any
    /// string slot, with or without a trailing comment, keeps its meaning.
    #[test]
    fn test_format_source_preserves_string_values(
        template in 0..TEMPLATES.len(),
        comment in 0..COMMENTS.len(),
        body in "[a-z ;#\n]{1,16}",
    ) {
        let (name, template) = TEMPLATES[template];
        let src = template.replace("{S}", &body).replace("{C}", COMMENTS[comment]);
        if let Err(e) = assert_format_preserves_meaning(name, &src) {
            prop_assert!(false, "{}", e);
        }
    }
}
