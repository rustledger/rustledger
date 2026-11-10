#!/usr/bin/env python3
"""Regenerate the BOM-combination matrix (#2928).

A mid-file BOM (U+FEFF) is reported by rledger through its own diagnostic
(`BomInDirectiveBody`), which also has to stand in for some of beancount's
`Invalid token` errors so that the counts agree. Each review round of #2931
found another combination of BOM tokens whose count drifted. This matrix
records beancount 3.2.3's per-line error counts for every combination of up
to three tokens, of the kinds below, in each of the line contexts below, with
each of the line-start prefixes below, and
`crates/rustledger-parser/tests/bom_combination_matrix.rs` checks rledger
against it row by row, without needing Python at test time.

Token kinds (`TOKENS`), `{i}` being the token's place on the line:

    L  a BOM-led invalid run           `<BOM>a{i}`
    I  a run with a BOM inside it       `x{i}<BOM>y`
    N  an invalid run with no BOM       `$n{i}`

Line-start prefixes (`PREFIXES`), put before the line, so before the
indentation of an indented line:

    plain           nothing
    bom             a BOM glued to whatever starts the line
    glued           a BOM glued to an invalid run, then a space (`<BOM>g `)
    glued-number    a BOM glued to a number, then an invalid run (`<BOM>12$ `)
    glued-currency  the same with a currency (`<BOM>USD$ `)

Contexts (`CONTEXTS`): the line on its own, after an invalid account, after
an invalid token, after a number (a grammar error), on a transaction header,
a posting, a metadata line, a metadata line holding an invalid account, a
directive's header, after a date alone, a metadata line under a header with
no narration, and an indented line whose first token is glued to a BOM after
the indentation (a run, and a `;`).

The counts are beancount's parse errors only, filtered exactly as the
parse-error parity harness (`scripts/compat-parse-error-parity.py`) filters
them: an invalid account name or option is a load-time error in rledger.

Run it where beancount 3.2.3 is installed (`nix develop .#bench`, or the
compat container):

    python3 -I scripts/bom-combination-matrix.py \\
        > crates/rustledger-parser/tests/data/bom_combination_matrix.tsv

Output, one line per case, tab-separated:

    <source>  <counts>

`<source>` is the input with each U+FEFF written `<BOM>` and each line break
`\\n` (no generated input holds a backslash, a `<` or a tab). `<counts>` is
`line:count` pairs, comma-separated, ascending, empty when beancount reports
nothing. Changing TOKENS, PREFIXES, CONTEXTS or HEAD here needs nothing in
the Rust test: it reads the sources from the table.
"""

import importlib.util
import itertools
import sys
from pathlib import Path

from beancount.parser import parser

REPO = Path(__file__).resolve().parent.parent

BOM = "\ufeff"

HEAD = "2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n"
TXN = '2024-01-02 * "n"\n'
TXN_BARE = "2024-01-02 *\n"
LEGS = "  Assets:A  1 USD\n  Assets:B\n"

TOKENS = {
    "L": BOM + "a{i}",
    "I": "x{i}" + BOM + "y",
    "N": "$n{i}",
}

PREFIXES = {
    "plain": "",
    "bom": BOM,
    "glued": BOM + "g ",
    # A BOM glued to a token that lexes here, then to an invalid one: one
    # invalid token in beancount, the whole blank-free run.
    "glued-number": BOM + "12$ ",
    "glued-currency": BOM + "USD$ ",
}

# (name, text before the line, the line with a `{T}` slot, text after it)
CONTEXTS = [
    ("top", "", "{T}", ""),
    ("account", "", "Ü:A {T}", ""),
    ("invalid", "", "foo {T}", ""),
    ("grammar", "", "313 {T}", ""),
    ("header", "", '2024-01-02 * "n" {T}', LEGS),
    ("posting", TXN, "  Assets:A  1 USD {T}", "  Assets:B\n"),
    ("meta", TXN, '  kk: "v" {T}', LEGS),
    ("meta-account", TXN, "  kk: Ü:A {T}", LEGS),
    ("directive", "", "2024-01-02 commodity EUR {T}", ""),
    # A date alone, where a directive keyword or flag is expected next.
    ("date", "", "2024-01-02 {T}", ""),
    # A metadata line under a header with no narration.
    ("meta-bare", TXN_BARE, '  kk: "v" {T}', LEGS),
    # A BOM after the indentation, glued to a run, and glued to a `;`.
    ("indent-bom", TXN_BARE, "  " + BOM + "b {T}", LEGS),
    ("indent-bom-comment", TXN_BARE, "  " + BOM + "; c {T}", LEGS),
]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def cases():
    """Every generated input, in table order."""
    for _, before, line, after in CONTEXTS:
        for prefix in PREFIXES.values():
            for n in range(4):
                for kinds in itertools.product(TOKENS, repeat=n):
                    tokens = " ".join(
                        TOKENS[k].format(i=i) for i, k in enumerate(kinds)
                    )
                    text = (prefix + line.format(T=tokens)).rstrip(" ")
                    if not text:
                        continue
                    yield HEAD + before + text + "\n" + after


def escape(src):
    assert "\\" not in src and "<" not in src and "\t" not in src, src
    return src.replace(BOM, "<BOM>").replace("\n", "\\n")


def main():
    parity = load("parity", REPO / "scripts/compat-parse-error-parity.py")
    is_not_syntax = load("matrix", REPO / "scripts/stray-char-matrix.py").is_not_syntax
    seen = set()
    for src in cases():
        if src in seen:
            continue
        seen.add(src)
        _, errors, _ = parser.parse_string(src)
        kept = parity.keep_parse_errors(errors, is_not_syntax)
        counts = {}
        for line, _, _ in kept:
            counts[line] = counts.get(line, 0) + 1
        cells = ",".join(f"{line}:{n}" for line, n in sorted(counts.items()))
        sys.stdout.write(f"{escape(src)}\t{cells}\n")


if __name__ == "__main__":
    main()
