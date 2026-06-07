//! Categorize divergent corpus files by which missing feature
//! is responsible. For each divergent file, examines the legacy
//! `ParseResult` and reports a histogram of which feature classes
//! appear (pre-posting comments, arithmetic AMOUNT, Document
//! tags/links, standalone comments, etc.). The output guides
//! which gap to attack next for maximum corpus-convergence
//! payoff.
//!
//! Diagnostic example only — lint rules tightened in the production
//! crate aren't worth enforcing for one-off probes.

#![allow(
    clippy::useless_let_if_seq,
    clippy::single_char_pattern,
    clippy::cast_lossless,
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::missing_panics_doc
)]

use std::collections::BTreeMap;
use std::path::PathBuf;

#[path = "../tests/baseline_common/mod.rs"]
mod baseline_common;

use baseline_common::{discover_corpus_files, repo_root};

fn main() {
    // `parse()` is env-gated to `parse_via_cst()` when this var
    // is set; that would make legacy output identical to CST
    // output and undercount divergence (every file would
    // classify as "no missing features").
    if std::env::var_os("RUSTLEDGER_CST_PARSER").is_some() {
        eprintln!(
            "error: RUSTLEDGER_CST_PARSER is set; this \
             categorizer needs it UNSET so that parse() invokes \
             the legacy parser. Re-run with the env var removed.",
        );
        std::process::exit(2);
    }
    let files = discover_corpus_files();
    let root = repo_root();

    let mut total_divergent = 0;
    let mut features: BTreeMap<&'static str, usize> = BTreeMap::new();
    // Also count files that have NONE of the known features
    // (mystery divergences worth a hand-inspection).
    let mut unclassified: Vec<PathBuf> = Vec::new();

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
        total_divergent += 1;

        let mut hit_any = false;

        if legacy.directives.iter().any(|d| match &d.value {
            rustledger_core::Directive::Transaction(t) => {
                t.postings.iter().any(|p| !p.value.comments.is_empty())
            }
            _ => false,
        }) {
            *features
                .entry("posting.comments (pre-posting `;`)")
                .or_default() += 1;
            hit_any = true;
        }

        if legacy.directives.iter().any(|d| match &d.value {
            rustledger_core::Directive::Transaction(t) => t
                .postings
                .iter()
                .any(|p| !p.value.trailing_comments.is_empty()),
            _ => false,
        }) {
            *features
                .entry("posting.trailing_comments (EOL `;`)")
                .or_default() += 1;
            hit_any = true;
        }

        if legacy.directives.iter().any(|d| match &d.value {
            rustledger_core::Directive::Transaction(t) => !t.trailing_comments.is_empty(),
            _ => false,
        }) {
            *features.entry("transaction.trailing_comments").or_default() += 1;
            hit_any = true;
        }

        if legacy
            .directives
            .iter()
            .any(|d| matches!(&d.value, rustledger_core::Directive::Document(doc) if !doc.tags.is_empty() || !doc.links.is_empty()))
        {
            *features.entry("Document tags/links").or_default() += 1;
            hit_any = true;
        }

        if !legacy.comments.is_empty() {
            *features
                .entry("ParseResult.comments (top-level `;`)")
                .or_default() += 1;
            hit_any = true;
        }

        // Arithmetic AMOUNT: heuristic — search the source text
        // for `<digit> [*/+-] <digit>` patterns inside posting
        // lines. Approximation only.
        if src.contains(" * ") && src.contains("USD") || src.contains(" + ") && src.contains(".") {
            // Better: count postings whose number isn't directly
            // comparable. We approximate by checking if the
            // source has expression-like patterns near postings.
            let suspect = src.lines().any(|line| {
                line.starts_with("  ") && {
                    let trimmed = line.trim_start();
                    trimmed.contains(" * ")
                        || trimmed.contains(" / ")
                        || trimmed.contains(" + ")
                        || trimmed.contains(" - ")
                }
            });
            if suspect {
                *features.entry("arithmetic AMOUNT (heuristic)").or_default() += 1;
                hit_any = true;
            }
        }

        // Section markers (`* Header` at top level — not in a txn).
        if src.lines().any(|line| line.starts_with("* ")) {
            *features
                .entry("section markers (`*` at col 0)")
                .or_default() += 1;
            hit_any = true;
        }

        // Pipe-separated payee/narration: `"payee" | "narration"`.
        if src.contains("\" | \"") || src.contains("\"|\"") {
            *features.entry("pipe payee separator").or_default() += 1;
            hit_any = true;
        }

        if !hit_any {
            unclassified.push(rel.clone());
        }
    }

    println!("Total divergent files: {total_divergent}");
    println!("\nFeature prevalence (files in which each missing feature appears):\n");
    // Sort descending by count.
    let mut sorted: Vec<_> = features.iter().collect();
    sorted.sort_by(|a, b| b.1.cmp(a.1));
    for (feature, count) in sorted {
        let pct = (*count as f64 / total_divergent as f64) * 100.0;
        println!("  {count:>4} ({pct:>5.1}%)  {feature}");
    }
    println!(
        "\nUnclassified (none of the above patterns matched): {}",
        unclassified.len()
    );
    println!("First 10 unclassified:");
    for p in unclassified.iter().take(10) {
        println!("  {}", p.display());
    }
}
