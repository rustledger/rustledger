//! The Beancount examples in the docs that are complete ledgers pass
//! `rledger check`.
//!
//! The syntax reference's `pad` example (and the cookbook's opening balance)
//! dated the pad and its balance on the same day, which `check` rejects (the
//! balance holds at the start of its day, so the pad is unused and the
//! balance fails), and its complete example asserted a month-end balance that
//! did not match its own transactions. Nothing ran them. Every block in
//! [`DOCS`] preceded by the marker
//! `<!-- docs-test: check-clean -->` is now checked with no errors and no
//! warnings. Blocks without it are fragments (a posting, a metadata line)
//! that are not ledgers on their own.
//!
//! The binary is `CARGO_BIN_EXE_rledger`, always built for this package's
//! integration tests, so nothing here can skip silently.

use std::path::Path;
use std::process::Command;

const MARKER: &str = "<!-- docs-test: check-clean -->";

/// The docs checked, relative to the workspace root.
const DOCS: &[&str] = &["docs/reference/syntax.md", "docs/guides/cookbook.md"];

/// Every marked block in `text`, as (1-based line of its fence, body).
fn marked_blocks(file: &str, text: &str) -> Vec<(usize, String)> {
    let mut blocks = Vec::new();
    let mut lines = text.lines().enumerate();
    while let Some((_, line)) = lines.next() {
        if line.trim() != MARKER {
            continue;
        }
        // The marker is followed (after blank lines) by the block it marks.
        let (fence_at, fence) = lines
            .by_ref()
            .find(|(_, l)| !l.trim().is_empty())
            .unwrap_or_else(|| panic!("{file}: {MARKER} at the end of the file"));
        assert_eq!(
            fence.trim(),
            "```beancount",
            "{file}:{}: {MARKER} must be followed by a beancount block",
            fence_at + 1
        );
        let body: Vec<&str> = lines
            .by_ref()
            .map(|(_, l)| l)
            .take_while(|l| l.trim() != "```")
            .collect();
        blocks.push((fence_at + 1, body.join("\n") + "\n"));
    }
    blocks
}

#[test]
fn test_marked_blocks_finds_each_marked_block() {
    let text = "intro\n\n<!-- docs-test: check-clean -->\n\n```beancount\n\
                2024-01-01 open Assets:Cash\n```\n\n```beancount\nnot marked\n```\n";
    let blocks = marked_blocks("t.md", text);
    assert_eq!(
        blocks,
        vec![(5, "2024-01-01 open Assets:Cash\n".to_string())]
    );
}

#[test]
fn test_docs_marked_examples_check_clean() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut checked = 0;
    for doc in DOCS {
        let text =
            std::fs::read_to_string(root.join(doc)).unwrap_or_else(|e| panic!("read {doc}: {e}"));
        let blocks = marked_blocks(doc, &text);
        assert!(!blocks.is_empty(), "{doc}: no {MARKER} blocks found");
        for (line, source) in blocks {
            let dir = tempfile::tempdir().expect("tempdir");
            let path = dir.path().join("example.beancount");
            std::fs::write(&path, &source).expect("write example");
            let out = Command::new(env!("CARGO_BIN_EXE_rledger"))
                .args(["check", "--no-cache", "--format", "json"])
                .arg(&path)
                .output()
                .expect("run rledger check");
            let stdout = String::from_utf8_lossy(&out.stdout);
            let value: serde_json::Value = serde_json::from_str(&stdout)
                .unwrap_or_else(|e| panic!("{doc}:{line}: check JSON: {e}\n{stdout}"));
            assert!(
                out.status.success() && value["error_count"] == 0 && value["warning_count"] == 0,
                "{doc}:{line}: the example does not check clean:\n{source}\n{stdout}"
            );
            checked += 1;
        }
    }
    assert!(checked > 0);
}
