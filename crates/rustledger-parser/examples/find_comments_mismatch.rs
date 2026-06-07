//! Find divergent files where ONLY the comments field differs.
//! Helps isolate top-level-comments extraction bugs from
//! everything else.

#![allow(
    clippy::useless_format,
    clippy::missing_panics_doc,
    clippy::print_stdout,
    clippy::manual_unwrap_or_default
)]

#[path = "../tests/baseline_common/mod.rs"]
mod baseline_common;

use baseline_common::{discover_corpus_files, repo_root};

fn main() {
    // `parse()` is env-gated to `parse_via_cst()` when this var
    // is set; that would make the legacy side identical to the
    // CST side and silently report no comments mismatches.
    if std::env::var_os("RUSTLEDGER_CST_PARSER").is_some() {
        eprintln!(
            "error: RUSTLEDGER_CST_PARSER is set; this probe \
             needs it UNSET so that parse() invokes the legacy \
             parser. Re-run with the env var removed.",
        );
        std::process::exit(2);
    }
    let files = discover_corpus_files();
    let root = repo_root();

    let mut by_size: Vec<(u64, std::path::PathBuf)> = Vec::new();
    for rel in files {
        let abs = root.join(rel);
        let Ok(src) = std::fs::read_to_string(&abs) else {
            continue;
        };
        let legacy = rustledger_parser::parse(&src);
        let cst = rustledger_parser::parse_via_cst(&src);
        let lp = rustledger_parser::__baseline_canonical_payload(&legacy);
        let cp = rustledger_parser::__baseline_canonical_payload(&cst);
        if lp == cp {
            continue;
        }
        if legacy.comments.len() != cst.comments.len() {
            let size = abs.metadata().map_or(u64::MAX, |m| m.len());
            by_size.push((size, rel.clone()));
        }
    }
    by_size.sort_by_key(|(s, _)| *s);
    println!(
        "Found {} files with comments-count mismatch:",
        by_size.len()
    );
    for (size, p) in by_size.iter().take(10) {
        println!("  {size:>6} bytes  {}", p.display());
    }
}
