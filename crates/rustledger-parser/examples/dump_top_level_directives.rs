//! Dump top-level directive boundaries from `parse_structured` in
//! TSV format. Intended for cross-validation against external
//! parsers (e.g. `polarmutex/tree-sitter-beancount`) via
//! `scripts/compat-treesitter.sh`.
//!
//! Output format (one line per top-level directive, sorted by
//! start byte):
//!
//! ```text
//! <kind>\t<start_byte>\t<end_byte>\t<first_line_excerpt>
//! ```
//!
//! - `<kind>` is the lowercased `SyntaxKind` name with `_directive`
//!   suffix stripped (e.g. `open`, `close`, `commodity`). Top-level
//!   tokens that are NOT inside a `*_DIRECTIVE` node are skipped
//!   (PR 2.1a's pass-through path for TRANSACTION / OPTION /
//!   INCLUDE / PLUGIN / CUSTOM / error-recovery lines).
//! - `<start_byte>` and `<end_byte>` are absolute byte offsets
//!   into the source.
//! - `<first_line_excerpt>` is the directive's first line of
//!   source text, truncated to 60 bytes for readability and with
//!   tabs/newlines escaped so each TSV row stays on one line.
//!
//! Usage:
//! ```text
//! cargo run --example dump_top_level_directives -- <path/to/file.beancount>
//! cat file.beancount | cargo run --example dump_top_level_directives -- -
//! ```

use std::env;
use std::fs;
use std::io::{self, Read};
use std::process::ExitCode;

use rustledger_parser::{SyntaxKind, parse_structured};

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!(
            "Usage: {} <path/to/file.beancount | ->\n  \
             '-' reads from stdin.",
            args[0],
        );
        return ExitCode::from(2);
    }

    let source = match args[1].as_str() {
        "-" => {
            let mut buf = String::new();
            if let Err(e) = io::stdin().read_to_string(&mut buf) {
                eprintln!("read stdin: {e}");
                return ExitCode::FAILURE;
            }
            buf
        }
        path => match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("read {path}: {e}");
                return ExitCode::FAILURE;
            }
        },
    };

    let tree = parse_structured(&source);
    for child in tree.children() {
        if let Some(kind_label) = directive_kind_label(child.kind()) {
            let range = child.text_range();
            let start = u32::from(range.start());
            let end = u32::from(range.end());
            let excerpt = first_line_excerpt(&source, start as usize, end as usize);
            println!("{kind_label}\t{start}\t{end}\t{excerpt}");
        }
    }
    ExitCode::SUCCESS
}

/// Returns the comparable kind label (e.g. `"open"`,
/// `"pushtag"`) for a structural directive node kind, or `None`
/// for non-directive node kinds we don't emit here.
///
/// Labels match the convention `polarmutex/tree-sitter-beancount`
/// uses for its top-level rule names, so the TSV columns are
/// directly diff-friendly.
const fn directive_kind_label(kind: SyntaxKind) -> Option<&'static str> {
    match kind {
        SyntaxKind::OPEN_DIRECTIVE => Some("open"),
        SyntaxKind::CLOSE_DIRECTIVE => Some("close"),
        SyntaxKind::BALANCE_DIRECTIVE => Some("balance"),
        SyntaxKind::PAD_DIRECTIVE => Some("pad"),
        SyntaxKind::EVENT_DIRECTIVE => Some("event"),
        SyntaxKind::QUERY_DIRECTIVE => Some("query"),
        SyntaxKind::NOTE_DIRECTIVE => Some("note"),
        SyntaxKind::DOCUMENT_DIRECTIVE => Some("document"),
        SyntaxKind::PRICE_DIRECTIVE => Some("price"),
        SyntaxKind::COMMODITY_DIRECTIVE => Some("commodity"),
        SyntaxKind::PUSHTAG_DIRECTIVE => Some("pushtag"),
        SyntaxKind::POPTAG_DIRECTIVE => Some("poptag"),
        SyntaxKind::PUSHMETA_DIRECTIVE => Some("pushmeta"),
        SyntaxKind::POPMETA_DIRECTIVE => Some("popmeta"),
        SyntaxKind::TRANSACTION => Some("transaction"),
        _ => None,
    }
}

/// Render the first line of the source between `start` and `end`
/// as a short, single-line excerpt with tabs/newlines escaped.
fn first_line_excerpt(source: &str, start: usize, end: usize) -> String {
    const MAX: usize = 60;
    let slice = &source[start..end];
    let first_line = slice.split('\n').next().unwrap_or(slice);
    let truncated = if first_line.len() > MAX {
        format!("{}…", &first_line[..MAX])
    } else {
        first_line.to_string()
    };
    truncated.replace('\t', "\\t").replace('\r', "\\r")
}
