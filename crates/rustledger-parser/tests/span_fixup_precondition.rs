//! The precondition `fixup_directive_spans`' binary search rests on.
//!
//! It looks a directive up in `all_starts` by the CST node's own start
//! offset. That list is built from `SourceFile::children()`, so it is sibling
//! order — and the search is only equivalent to the linear `position()` scan
//! it replaced if starts are strictly ascending and unique.
//!
//! They differ only if two sibling directives share a start, which requires a
//! ZERO-WIDTH `Directive`-castable node. `position()` would have returned the
//! first; `binary_search` returns an arbitrary one. Error recovery is where
//! such a node could plausibly appear, so this hammers recovery paths rather
//! than well-formed ledgers.
//!
//! The `debug_assert` in `fixup_directive_spans` covers the same ground in
//! debug builds; this checks the condition DIRECTLY so a release-mode
//! regression, or a change that removes the assert, still gets caught.

use rustledger_parser::cst::ast::{AstNode as _, Directive};
use rustledger_parser::parse;

/// Returns a description of the first violation found, if any.
fn violation(src: &str) -> Option<String> {
    let parsed = parse(src);
    let mut prev: Option<u32> = None;
    for n in parsed.syntax_node().children() {
        if !Directive::can_cast(n.kind()) {
            continue;
        }
        let range = n.text_range();
        let start: u32 = range.start().into();
        if u32::from(range.len()) == 0 {
            return Some(format!("zero-width {:?} at {start} in {src:?}", n.kind()));
        }
        if let Some(p) = prev
            && start <= p
        {
            return Some(format!("start {start} not after {p} in {src:?}"));
        }
        prev = Some(start);
    }
    None
}

/// Deterministic LCG. Not `rand`: this must reproduce byte-for-byte on CI,
/// and a failure has to be replayable from the seed alone.
struct Lcg(u64);
impl Lcg {
    const fn next(&mut self) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) as usize
    }
}

#[test]
fn directive_siblings_never_share_a_start() {
    // Fragments chosen to end up mid-directive: bare keywords, unterminated
    // strings, unbalanced braces, a BOM, and empties — the shapes that make
    // the parser open a node and then recover.
    const ATOMS: &[&str] = &[
        "pushtag",
        "poptag",
        "pushmeta",
        "popmeta",
        "2024-01-01",
        "open",
        "close",
        "*",
        "\"",
        "{",
        "}",
        "{{",
        "}}",
        "^a",
        "#a",
        "\n",
        " ",
        "\r\n",
        "\u{feff}",
        "",
        ";x",
        "custom",
        "Assets:B",
        "1 USD",
        ":",
        ",",
        "balance",
        "pad",
        "price",
        "@",
        "@@",
    ];

    // Hand-picked cases first — the ones most likely to produce an empty node.
    for src in [
        "",
        "\n",
        "\n\n\n",
        "pushtag",
        "poptag\n",
        "pushmeta",
        "popmeta\n",
        "2024-01-01",
        "2024-01-01\n",
        "2024-01-01 ",
        "2024-01-01 open",
        "2024-01-01 * \"",
        "\u{feff}",
        "\u{feff}\n\n",
        "\r\n\r\n",
        "*\n*\n*\n",
        "{{{\n",
        "pushtagpoptag\n",
        "2024-01-012024-01-02\n",
        "pushtag #a\npoptag #a\npushtag #b\npoptag #b\n",
    ] {
        assert!(violation(src).is_none(), "{}", violation(src).unwrap());
    }

    let mut rng = Lcg(0x2545_F491_4F6C_DD1D);
    for _ in 0..20_000 {
        let len = rng.next() % 12 + 1;
        let src: String = (0..len).map(|_| ATOMS[rng.next() % ATOMS.len()]).collect();
        assert!(violation(&src).is_none(), "{}", violation(&src).unwrap());
    }
}

/// The check above is worthless if it cannot report a violation, and it
/// cannot be shown to by feeding it real source — the whole point is that no
/// input produces one. So feed the DETECTOR a sequence it must reject.
#[test]
fn the_violation_detector_can_actually_fail() {
    // Same shape as `violation`'s loop, run over a hand-built sequence with a
    // duplicate start. If this logic ever stops flagging that, the test above
    // is asserting nothing.
    let starts = [0u32, 10, 10, 20];
    let mut prev: Option<u32> = None;
    let mut flagged = false;
    for start in starts {
        if let Some(p) = prev
            && start <= p
        {
            flagged = true;
        }
        prev = Some(start);
    }
    assert!(
        flagged,
        "the ascending check must reject a duplicate start; if it does not, \
         `directive_siblings_never_share_a_start` proves nothing",
    );
}
