//! Find divergent files where ONLY the comments field differs.
//! Helps isolate top-level-comments extraction bugs from
//! everything else.

#![allow(clippy::useless_format, clippy::missing_panics_doc)]

#[path = "../tests/baseline_common/mod.rs"]
mod baseline_common;

use baseline_common::{discover_corpus_files, repo_root};

fn main() {
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
            let size = abs.metadata().map(|m| m.len()).unwrap_or(u64::MAX);
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
