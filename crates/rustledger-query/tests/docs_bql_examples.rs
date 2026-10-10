//! The BQL examples in the docs parse when pasted (#2403).
//!
//! BQL's comments are `/* ... */`, as in bean-query. `--` is not one: it
//! reads `3--2` as `3 - -2`, so a `-- note` line is part of the query. The
//! docs annotated their examples with `-- ...`, which made every such example
//! fail to parse. This reads every ```sql block of the BQL docs, refuses a
//! `--` annotation, and parses each complete statement in it. A block may
//! also hold clause fragments (`WHERE ...`) and syntax sketches
//! (`BALANCES [FROM ...]`); those are not statements and are skipped.

use rustledger_query::parse;
use rustledger_query::parser::strip_comments;

/// The docs whose ```sql blocks are BQL. (`docs/development/
/// import-architecture.md`'s are SQLite schemas.)
const BQL_DOCS: &[&str] = &[
    "docs/reference/bql.md",
    "docs/commands/query.md",
    "docs/guides/common-queries.md",
    "docs/guides/budgeting.md",
];

const STATEMENT_STARTS: &[&str] = &["SELECT", "BALANCES", "JOURNAL", "PRINT"];

/// Syntax templates, not queries: the first line of each.
const TEMPLATES: &[&str] = &["SELECT columns"];

fn starts_statement(line: &str) -> bool {
    let line = line.trim_start();
    STATEMENT_STARTS.iter().any(|kw| {
        line.get(..kw.len())
            .is_some_and(|s| s.eq_ignore_ascii_case(kw))
            && line[kw.len()..]
                .chars()
                .next()
                .is_none_or(char::is_whitespace)
    })
}

/// The statements of a block: a blank line ends one, and a line starting
/// with a statement keyword starts the next.
fn statements(block: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut current = String::new();
    for line in block.lines() {
        if line.trim().is_empty() || starts_statement(line) {
            if !current.trim().is_empty() {
                out.push(std::mem::take(&mut current));
            }
            current.clear();
        }
        current.push_str(line);
        current.push('\n');
    }
    if !current.trim().is_empty() {
        out.push(current);
    }
    out
}

fn sql_blocks(text: &str) -> Vec<(usize, String)> {
    let mut blocks = Vec::new();
    let mut current: Option<(usize, String)> = None;
    for (i, line) in text.lines().enumerate() {
        let fence = line.trim_start().strip_prefix("```");
        match (&mut current, fence) {
            (None, Some(lang)) if lang.trim() == "sql" => current = Some((i + 2, String::new())),
            (Some(_), Some(_)) => blocks.push(current.take().expect("open block")),
            (Some((_, body)), None) => {
                body.push_str(line);
                body.push('\n');
            }
            _ => {}
        }
    }
    blocks
}

#[test]
fn every_bql_doc_example_parses() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut parsed = 0;
    let mut failures = Vec::new();
    for doc in BQL_DOCS {
        let text = std::fs::read_to_string(root.join(doc)).expect("doc exists");
        for (first_line, block) in sql_blocks(&text) {
            for (k, line) in block.lines().enumerate() {
                assert!(
                    !line.trim_start().starts_with("--") && !line.contains(" -- "),
                    "{doc}:{}: `--` is not a BQL comment; use /* ... */: {line}",
                    first_line + k,
                );
            }
            let stripped = strip_comments(&block)
                .unwrap_or_else(|e| panic!("{doc}:{first_line}: {e}"))
                .into_owned();
            for statement in statements(&stripped) {
                let statement = statement.trim();
                let sketch = ["[", "...", "<", "|"].iter().any(|m| statement.contains(m))
                    || TEMPLATES.iter().any(|t| statement.starts_with(t));
                if !starts_statement(statement) || sketch {
                    continue;
                }
                parsed += 1;
                if let Err(e) = parse(statement) {
                    failures.push(format!("{doc}:{first_line}: {e}\n{statement}"));
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    assert!(
        parsed > 40,
        "only {parsed} statements found; did the docs move?"
    );
}
