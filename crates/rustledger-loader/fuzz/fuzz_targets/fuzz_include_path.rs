//! The `include` path-traversal guard, over arbitrary include strings.
//!
//! `CLAUDE.md` states the requirement plainly: "Loader: Must prevent path
//! traversal in `include` directives." The guard that enforces it is subtle
//! enough to deserve a fuzzer rather than examples — it branches on whether
//! the path looks like a glob, and for globs it slices the string at the first
//! `*?[`, then again at the last `/` before that, and normalizes the result
//! through an injected filesystem. Each of those steps is a place where an
//! unusual string can take an unintended branch.
//!
//! This asserts the SECURITY PROPERTY, not merely the absence of panics:
//! whatever the include string, no file outside the configured root may be
//! loaded. A fuzzer that only checked for crashes would happily accept a
//! traversal that silently succeeded.
//!
//! Runs entirely against `VirtualFileSystem`, so it touches no disk and the
//! "outside the root" files are ones we planted deliberately.
#![no_main]

use libfuzzer_sys::fuzz_target;
use rustledger_loader::{Loader, VirtualFileSystem};
use std::path::PathBuf;

fuzz_target!(|include: String| {
    // Escape EXACTLY what the Beancount lexer decodes, so the loader sees the
    // fuzz string verbatim.
    //
    // `escape_default()` was wrong here: it emits `\u{..}` and `\x..`, which
    // the lexer does not decode — on an unknown escape `decode_string_token`
    // drops the backslash and keeps the character, so `\u{41}` reached the
    // loader as the literal `u{41}`. The fuzzer was exploring a distorted
    // space and reporting coverage it did not have.
    let Some(literal) = escape_for_beancount(&include) else {
        return;
    };

    let root = PathBuf::from("/ledger");

    let mut fs = VirtualFileSystem::new();
    // Inside the root: the legitimate ledger.
    fs.add_file("/ledger/main.beancount", format!("include \"{literal}\"\n"));
    fs.add_file("/ledger/ok.beancount", "2020-01-01 open Assets:In\n");
    fs.add_file("/ledger/sub/ok.beancount", "2020-01-01 open Assets:Sub\n");
    // Outside the root: must never be reachable, however the include is spelled.
    fs.add_file("/secret.beancount", "2020-01-01 open Assets:Secret\n");
    fs.add_file("/etc/passwd.beancount", "2020-01-01 open Assets:Passwd\n");
    fs.add_file("/ledger-sibling/x.beancount", "2020-01-01 open Assets:Sibling\n");

    let mut loader = Loader::new()
        .with_filesystem(Box::new(fs)).with_root_dir(root.clone());
    let Ok(result) = loader.load(&PathBuf::from("/ledger/main.beancount")) else {
        // A refusal is always an acceptable outcome; only a successful escape
        // is a bug.
        return;
    };

    // Assert the property directly — "none of the files I planted OUTSIDE the
    // root was loaded" — rather than string-prefix matching the loaded paths.
    //
    // The first version prefix-matched `/ledger/` and the fuzzer refuted it on
    // the empty include: the source map records `ledger/main.beancount`, with
    // the leading slash normalized away, so a legitimately-inside file looked
    // like an escape. Prefix matching tests the path FORMATTING; naming the
    // forbidden files tests the security boundary, and is immune to however
    // the loader chooses to spell a path.
    const OUTSIDE: &[&str] = &["secret.beancount", "passwd.beancount", "x.beancount"];
    for file in result.source_map.files() {
        let path = file.path.to_string_lossy();
        for forbidden in OUTSIDE {
            assert!(
                !path.ends_with(forbidden),
                "include {include:?} escaped the root: loaded {path:?}"
            );
        }
    }
});

/// Escape a string so the Beancount lexer reproduces it exactly.
///
/// The lexer decodes `\"`, `\\`, `\n`, `\t`, `\r` and, for any other
/// escape, drops the backslash and keeps the character. So only those five
/// may be emitted; a control character that is not one of them cannot survive
/// the round trip, and cannot appear in a real path either, so those inputs
/// are skipped rather than silently mangled.
fn escape_for_beancount(s: &str) -> Option<String> {
    let mut out = String::with_capacity(s.len() + 8);
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if c.is_control() => return None,
            c => out.push(c),
        }
    }
    Some(out)
}
