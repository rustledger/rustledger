#!/usr/bin/env python3
"""Regenerate the BOM-combination matrix (#2928).

A mid-file BOM (U+FEFF) is reported by rledger through its own diagnostic
(`BomInDirectiveBody`), which also has to stand in for some of beancount's
`Invalid token` errors so that the counts agree. Each review round of #2931
found another combination of BOM tokens whose count drifted. This table
records beancount 3.2.3's per-line error counts for three sets of inputs, and
`crates/rustledger-parser/tests/bom_combination_matrix.rs` checks rledger
against it row by row, without needing Python at test time.

1. The matrix (`matrix_cases`): token combinations, in each of the line
   contexts below, with each of the line-start prefixes below. Every
   combination of up to two tokens of all kinds, and of three tokens of the
   first three kinds. `{i}` is the token's place on the line:

       L  a BOM-led invalid run              `<BOM>a{i}`
       I  a run with a BOM inside it          `x{i}<BOM>y`
       N  an invalid run with no BOM          `$n{i}`
       K  a BOM-led account (an ACCOUNT in    `<BOM>Assets:A{i}`
          beancount, whose account type
          admits a non-ASCII first character)
       C  a lone capital glued to a BOM       `A<BOM>b{i}`

   Line-start prefixes (`PREFIXES`), put before the line, so before the
   indentation of an indented line:

       plain           nothing
       bom             a BOM glued to whatever starts the line
       glued           a BOM glued to an invalid run, then a space (`<BOM>g `)
       glued-number    a BOM glued to a number, then an invalid run (`<BOM>12$ `)
       glued-currency  the same with a currency (`<BOM>USD$ `)

   Contexts (`CONTEXTS`): the line on its own, after an invalid account, after
   an invalid token, after a number (a grammar error), on a transaction
   header, a posting, a metadata line, a metadata line holding an invalid
   account, a directive's header, after a date alone, a metadata line under a
   header with no narration, and an indented line whose first token is glued
   to a BOM after the indentation (a run, and a `;`).

2. Hand-picked inputs (`EXTRA`): each shape a review of #2931 found, so that
   each stays pinned whatever the generators above cover.

3. A seeded random probe (`probe_cases`, seed `PROBE_SEED`, `PROBE_COUNT`
   inputs): lines of four or five tokens drawn from BOM tokens and ordinary
   ones (strings, comments, headings, `#!` / `#+`, `%`, push directives, cost
   and price, tags, links), joined by mixed blanks, under every directive type
   with indented metadata and posting lines, with CRLF line endings or none at
   the end of the file now and then. It holds whatever the hand-made sets
   miss, so a future count change anywhere shows up in the test.

The counts are beancount's parse errors only, filtered exactly as the
parse-error parity harness (`scripts/compat-parse-error-parity.py`) filters
them: an invalid account name or option is a load-time error in rledger.
Each input is parsed in a forked child, as beancount's C parser can crash; an
input it crashes or raises on is left out (an unclosed `pushmeta` makes its
builder raise; the script names each one on stderr).

Run it where beancount 3.2.3 is installed (`nix develop .#bench`, or the
compat container):

    python3 -I scripts/bom-combination-matrix.py \\
        > crates/rustledger-parser/tests/data/bom_combination_matrix.tsv

Output, one line per case, tab-separated:

    <source>  <counts>

`<source>` is the input with each U+FEFF written `<BOM>`, each `\\n` written
`\\\\n`, each `\\r` `\\\\r` and each tab `\\\\t` (no generated input holds a
backslash or a `<`). `<counts>` is `line:count` pairs, comma-separated,
ascending, empty when beancount reports nothing. Changing the sets here needs
nothing in the Rust test: it reads the sources from the table.
"""

import importlib.util
import itertools
import json
import os
import random
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
    "K": BOM + "Assets:A{i}",
    "C": "A" + BOM + "b{i}",
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

# Shapes the reviews of #2931 found, after HEAD.
EXTRA = [
    "$x " + BOM + "Assets:A\n",
    BOM + "\t" + BOM + "Assets:A\n",
    "2024-01-02 open " + BOM + "Assets:C\n",
    "2024-01-02 *\n  " + BOM + "Assets:A  1 USD\n  Assets:B\n",
    BOM + "A\n",
    BOM + "USD\n",
    "$x " + BOM + "Assets:\n",
    "$x A" + BOM + "b\n",
    "@ ! A" + BOM + "b %x\n",
    BOM + "*7" + BOM + "* #tag\n",
    BOM + "**" + BOM + "*\t\"s" + BOM + "t\"\n",
    BOM + "* Heading with words\n",
    BOM + BOM + BOM + BOM + "*7 Z#\n",
    BOM + "12$ 2024-01-02 open Assets:C USD #tag\n",
    "$x 2024-01-02 open Assets:C USD #tag\n",
    "2024-01-02 " + BOM + "a x" + BOM + "y\n",
    "2024-01-02 *\n" + BOM + "  k: Ü:A " + BOM + "a0 x" + BOM + "y1\n",
    "2024-01-02 *\n  " + BOM + "; c\n",
    "2024-01-02 price USD 1 " + BOM + "EUR\n  source: \"x\"\n",
    "2024-01-02 query \"q\" " + BOM + "\"select 1\"\r\n  kk: 1\r\n",
]

PROBE_SEED = 2931
PROBE_COUNT = 2000

PROBE_BOM_TOKENS = [
    BOM + "a",
    "x" + BOM + "y",
    BOM + "Assets:A",
    "A" + BOM + "b",
    BOM,
    BOM + "*",
    BOM + '"s"',
    BOM + "12$",
    BOM + "#t",
    BOM + "Ü:A",
]
PROBE_TOKENS = [
    "2024-01-02",
    "open",
    "Assets:A",
    "USD",
    "1",
    "-2.5",
    '"s"',
    '"a' + BOM + 'b"',
    "#t",
    "^l",
    "@",
    "@@",
    "{1 USD}",
    "!",
    "*",
    "%",
    "$x",
    "foo",
    "Ü:A",
    ";c",
    "#!d",
    "#+x",
    "kk:",
    "A",
    "T#!",
    "(1 + 2)",
    "~",
    ",",
    "|",
]
PROBE_HEADERS = [
    "2024-01-02 open Assets:C USD",
    "2024-01-02 close Assets:C",
    "2024-01-02 commodity EUR",
    "2024-01-02 balance Assets:A 1 USD",
    "2024-01-02 pad Assets:A Assets:B",
    '2024-01-02 note Assets:A "n"',
    '2024-01-02 document Assets:A "d.pdf"',
    "2024-01-02 price USD 1 EUR",
    '2024-01-02 event "e" "v"',
    '2024-01-02 query "q" "select 1"',
    '2024-01-02 custom "b" 1',
    '2024-01-02 * "p" "n"',
    "2024-01-02 *",
    "2024-01-02 ! #t ^l",
    'option "title" "T"',
    'plugin "p"',
    "pushtag #t",
    "poptag #t",
    "pushmeta kk: 1",
    "popmeta kk:",
    "* Heading",
]
PROBE_INDENTED = [
    '  kk: "v"',
    "  Assets:A  1 USD",
    "  Assets:A  1 HOOL {2 USD} @ 3 USD",
    "  Assets:A  1 HOOL {{2 USD}} @@ 3 USD",
    "    pk: 2",
    "  #t ^l",
    "  ; c",
]
PROBE_SEPARATORS = [" ", " ", "  ", "\t", " \t"]
PROBE_PREFIXES = ["", "", "", BOM, "  ", "  " + BOM, "\t", BOM + "  "]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def matrix_cases():
    """The matrix inputs, in table order."""
    short = list(itertools.chain.from_iterable(
        itertools.product(TOKENS, repeat=n) for n in range(3)
    ))
    long = list(itertools.product("LIN", repeat=3))
    for _, before, line, after in CONTEXTS:
        for prefix in PREFIXES.values():
            for kinds in short + long:
                tokens = " ".join(TOKENS[k].format(i=i) for i, k in enumerate(kinds))
                text = (prefix + line.format(T=tokens)).rstrip(" ")
                if not text:
                    continue
                yield HEAD + before + text + "\n" + after


def probe_tokens(rng, n):
    out = []
    for _ in range(n):
        pool = PROBE_BOM_TOKENS if rng.random() < 0.4 else PROBE_TOKENS
        out.append(rng.choice(pool))
    return out


def probe_line(rng, start=None):
    """One probe line: an optional start, then four or five tokens."""
    words = ([start] if start else []) + probe_tokens(rng, rng.choice([4, 5]))
    text = words[0]
    for word in words[1:]:
        text += rng.choice(PROBE_SEPARATORS) + word
    return text


def probe_cases():
    """The seeded random probe inputs, in table order."""
    rng = random.Random(PROBE_SEED)
    for _ in range(PROBE_COUNT):
        lines = []
        for _ in range(rng.choice([1, 2, 3])):
            kind = rng.random()
            if kind < 0.35:
                lines.append(rng.choice(PROBE_PREFIXES) + probe_line(rng))
            else:
                header = rng.choice(PROBE_HEADERS)
                if rng.random() < 0.5:
                    header = probe_line(rng, header)
                lines.append(rng.choice(["", "", BOM]) + header)
                for _ in range(rng.choice([0, 1, 2])):
                    indented = rng.choice(PROBE_INDENTED)
                    if rng.random() < 0.6:
                        indented = probe_line(rng, indented)
                    lines.append(rng.choice(["", "", BOM]) + indented)
        eol = "\r\n" if rng.random() < 0.2 else "\n"
        body = eol.join(lines)
        if rng.random() < 0.8:
            body += eol
        yield HEAD + body


def escape(src):
    assert "\\" not in src and "<" not in src, src
    return (
        src.replace(BOM, "<BOM>")
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
    )


def counts_in_child(parity, is_not_syntax, src):
    """beancount's per-line counts for `src`, parsed in a forked child, or
    None when the parser crashes or raises."""
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        try:
            _, errors, _ = parser.parse_string(src)
            kept = parity.keep_parse_errors(errors, is_not_syntax)
            payload = json.dumps([line for line, _, _ in kept])
        except Exception:  # the parser raised: no verdict
            payload = "null"
        with os.fdopen(w, "w") as f:
            f.write(payload)
        os._exit(0)
    os.close(w)
    with os.fdopen(r) as f:
        payload = f.read()
    _, status = os.waitpid(pid, 0)
    if status != 0 or not payload or payload == "null":
        return None
    counts = {}
    for line in json.loads(payload):
        counts[line] = counts.get(line, 0) + 1
    return ",".join(f"{line}:{n}" for line, n in sorted(counts.items()))


def main():
    parity = load("parity", REPO / "scripts/compat-parse-error-parity.py")
    is_not_syntax = load("matrix", REPO / "scripts/stray-char-matrix.py").is_not_syntax
    seen = set()
    sources = itertools.chain(
        matrix_cases(), (HEAD + extra for extra in EXTRA), probe_cases()
    )
    for src in sources:
        if src in seen:
            continue
        seen.add(src)
        cells = counts_in_child(parity, is_not_syntax, src)
        if cells is None:
            print(f"left out, beancount crashed or raised: {src!r}", file=sys.stderr)
            continue
        sys.stdout.write(f"{escape(src)}\t{cells}\n")


if __name__ == "__main__":
    main()
