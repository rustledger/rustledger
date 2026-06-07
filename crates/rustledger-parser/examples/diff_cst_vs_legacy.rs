//! Quick diagnostic: print the first N character of the diff
//! between the legacy parser's canonical payload and the
//! `parse_via_cst` payload for a single source file. Used during
//! phase 3.2-3.4 migration to bisect which feature is missing
//! from a divergent corpus file.
//!
//! ## Usage
//!
//! ```text
//! cargo run --example diff_cst_vs_legacy -- path/to/file.beancount
//! ```

use std::path::PathBuf;

fn main() {
    // `parse()` is env-gated to `parse_via_cst()` when this var
    // is set; that would make the legacy column of this diff
    // ALSO be CST output and silently report no divergence.
    if std::env::var_os("RUSTLEDGER_CST_PARSER").is_some() {
        eprintln!(
            "error: RUSTLEDGER_CST_PARSER is set; this diagnostic \
             needs it UNSET so that parse() invokes the legacy \
             parser. Re-run with the env var removed.",
        );
        std::process::exit(2);
    }
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: diff_cst_vs_legacy <path-to-beancount-file>");
        std::process::exit(2);
    }
    let path = PathBuf::from(&args[1]);
    let source = std::fs::read_to_string(&path).expect("read source");

    let legacy = rustledger_parser::parse(&source);
    let cst = rustledger_parser::parse_via_cst(&source);

    eprintln!(
        "directive counts: legacy={} cst={}",
        legacy.directives.len(),
        cst.directives.len()
    );
    eprintln!(
        "options counts:   legacy={} cst={}",
        legacy.options.len(),
        cst.options.len()
    );
    eprintln!(
        "comments counts:  legacy={} cst={}",
        legacy.comments.len(),
        cst.comments.len()
    );
    eprintln!(
        "currency_occurrences: legacy={} cst={}",
        legacy.currency_occurrences.len(),
        cst.currency_occurrences.len()
    );

    let lp = rustledger_parser::__baseline_canonical_payload(&legacy);
    let cp = rustledger_parser::__baseline_canonical_payload(&cst);

    let lp_s = String::from_utf8_lossy(&lp).to_string();
    let cp_s = String::from_utf8_lossy(&cp).to_string();

    // Optionally dump full payloads to files for offline diff.
    if std::env::var_os("DIFF_DUMP").is_some() {
        std::fs::write("/tmp/legacy_payload.txt", &lp).ok();
        std::fs::write("/tmp/cst_payload.txt", &cp).ok();
        eprintln!("payloads written to /tmp/legacy_payload.txt /tmp/cst_payload.txt");
    }

    if lp == cp {
        println!("IDENTICAL ({} bytes)", lp.len());
        return;
    }

    // Find first divergent byte.
    let common = lp_s
        .as_bytes()
        .iter()
        .zip(cp_s.as_bytes().iter())
        .take_while(|(a, b)| a == b)
        .count();

    println!("DIVERGENT");
    println!("  legacy payload: {} bytes", lp.len());
    println!("  cst payload:    {} bytes", cp.len());
    println!("  first diff at byte: {common}");
    println!();

    // Show a window of context around the divergence.
    let win = 200;
    let start = common.saturating_sub(win / 2);
    let end_l = (common + win).min(lp_s.len());
    let end_c = (common + win).min(cp_s.len());

    println!("--- legacy [{start}..{end_l}] ---");
    println!("{}", &lp_s[start..end_l]);
    println!();
    println!("--- cst    [{start}..{end_c}] ---");
    println!("{}", &cp_s[start..end_c]);
}
