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
       k  a BOM-led account beancount reads   `<BOM>assets:A{i}`
          only with its BOM (no account of
          rledger's follows the BOM)
       T  a BOM-led account with an invalid   `<BOM>Assets:A{i}$x`
          tail glued to it
       t  the same for an account beancount   `<BOM>assets:A{i}$x`
          reads only with its BOM

   and, alone on a line (`TAIL_TOKENS`), that account with a tail that makes
   its end observable: `<BOM>"s"`, `~<BOM>1:A`, `<BOM>x`, and a later BOM-led
   account ending at a comment with a token after it (`~<BOM>1:A;c $x`,
   `,<BOM>a-b:C;c $x`).

   Line-start prefixes (`PREFIXES`), put before the line, so before the
   indentation of an indented line:

       plain           nothing
       bom             a BOM glued to whatever starts the line
       glued           a BOM glued to an invalid run, then a space (`<BOM>g `)
       glued-number    a BOM glued to a number, then an invalid run (`<BOM>12$ `)
       bom-bom         two BOMs glued to whatever starts the line

   Contexts (`CONTEXTS`): the line on its own, after an invalid account, after
   an invalid token, after a number (a grammar error), on a transaction
   header, a posting, a metadata line, a metadata line holding an invalid
   account, a directive's header, after a date alone, a metadata line under a
   header with no narration, and an indented line whose first token is glued
   to a BOM after the indentation (a run, and a `;`), and a `<BOM>*` heading
   line, plain and after a `{#t` (a brace and a tag in beancount).

2. Hand-picked inputs (`EXTRA`): each shape a review of #2931 found, so that
   each stays pinned whatever the generators above cover.

3. A seeded random probe (`probe_cases`, seed `PROBE_SEED`, `PROBE_COUNT`
   inputs): lines of four or five tokens drawn from BOM tokens and ordinary
   ones (strings, comments, headings, `#!` / `#+`, `%`, push directives, cost
   and price, tags, links), joined by mixed blanks, under every directive type
   with indented metadata and posting lines, with CRLF line endings or none at
   the end of the file now and then. It holds whatever the hand-made sets
   miss, so a future count change anywhere shows up in the test.

4. A second seeded probe (`account_probe_cases`, seed `ACCOUNT_PROBE_SEED`):
   a BOM-led account as beancount reads it, after each kind of line start
   (none, one or two BOMs, an invalid token, a `<BOM>*` heading, a custom
   directive, an indented line, a metadata value), followed by one to three
   tails glued to it or after a blank.

The counts are beancount's parse errors only, filtered exactly as the
parse-error parity harness (`scripts/compat-parse-error-parity.py`) filters
them: an invalid account name or option is a load-time error in rledger.
Each input is parsed in a forked child, as beancount's C parser can crash; an
input it crashes or raises on is left out (an unclosed `pushmeta` makes its
builder raise; the script names each one on stderr).

Run it where beancount 3.2.3 is installed (`nix develop .#bench`, or the
compat container):

    python3 -I scripts/bom-combination-matrix.py --main-binary MAIN_BINARY \\
        > crates/rustledger-parser/tests/data/bom_combination_matrix.tsv

Pass `--main-binary` the `parse_error_lines` example built from the main
branch the matrix is checked against (`cargo build --release -p
rustledger-loader --no-default-features --example parse_error_lines` there):
its counts, and both sides' counts for the input with its BOMs replaced by
ordinary characters (`analog`), let the test tell a line rledger counts
further from beancount than main only because main miscounted a BOM. The
last column, beancount's counts with each mid-line `#!` / `#+` made an
ordinary invalid run (`hash_bang_analog`), lets it tell a line whose whole
difference is part 2 of #2928. The column after it, beancount's count for
each line alone (`alone_cells`: after the head, under a bare `2024-01-02 *`
header when indented), lets it tell a line whose difference comes only from
the lines before it (beancount's error recovery, #2872).

Output, one line per case, tab-separated:

    <source>  <beancount>  <main>  <beancount analog>  <main analog>  <beancount hash-bang analog>  <beancount alone>  <BOM accounts>  <inner BOMs>  <later grammar>

`<source>` is the input with each U+FEFF written `<BOM>`, each `\\n` written
`\\\\n`, each `\\r` `\\\\r` and each tab `\\\\t` (no generated input holds a
backslash or a `<`). Each count column is `line:count` pairs,
comma-separated, ascending, empty when there is no error; an unclosed
`pushtag` / `pushmeta` is line 0 on both sides, as in the parity harness.
`<beancount alone>` lists every line after the head, a zero included, and
leaves out a line beancount crashes or raises on alone. The last two columns
say where beancount's own lexer (`lexer.lex_iter_string`) puts the BOMs, as
byte offsets into the input: `<BOM accounts>` the `ACCOUNT` tokens that start
with a BOM (`start-end`), `<inner BOMs>` the BOMs inside an invalid token
past its leading BOMs; so the test reads beancount's token boundaries instead
of guessing them. `<later grammar>` counts, per line, beancount's grammar
errors after the line's first error (`later_grammar_cells`).
Changing the sets here needs nothing in the Rust test: it reads the sources
from the table.
"""

import argparse
import importlib.util
import itertools
import json
import os
import random
import re
import subprocess
import sys
from pathlib import Path

from beancount.parser import lexer, parser

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
    "k": BOM + "assets:A{i}",
    "T": BOM + "Assets:A{i}$x",
    "t": BOM + "assets:A{i}$x",
}

# Tails after a BOM-led account beancount reads only with its BOM, each
# making the split at the account's end observable; matrix singles only.
TAIL_TOKENS = {
    "s": BOM + "assets:A{i}" + BOM + "\"s\"",
    "u": BOM + "assets:A{i}~" + BOM + "1:A",
    "x": BOM + "assets:A{i}" + BOM + "x",
    # A comment after a later BOM-led account of the tail takes the rest of
    # the line, a token after it included.
    "v": BOM + "assets:A{i}~" + BOM + "1:A;c $x",
    "w": BOM + "assets:A{i}," + BOM + "a-b:C;c $x",
}

PREFIXES = {
    "plain": "",
    "bom": BOM,
    "glued": BOM + "g ",
    # A BOM glued to a token that lexes here, then to an invalid one: one
    # invalid token in beancount, the whole blank-free run.
    "glued-number": BOM + "12$ ",
    # Two BOMs, so a run of line-start BOMs comes before each token.
    "bom-bom": BOM + BOM,
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
    # A `<BOM>*` heading line, whose rest beancount lexes after the first
    # blank.
    ("heading", "", BOM + "* Heading {T}", ""),
    # The same after a `{#t`, which beancount lexes as a `{` and a tag.
    ("heading-brace-hash", "", BOM + "* H {{#t {T}", ""),
    # A BOM-led account line right after a line beancount cannot read, which
    # its recovery skips in silence (#2872).
    ("after-error", "foo\n", BOM + "assets:A {T}", ""),
    # Two differences on one line: a glued BOM with a mid-line `#+`, and a
    # glued BOM where a price expects its amount, with a construct error.
    ("glued-hash-bang", TXN_BARE, "  " + BOM + "1:A:B  #+x {T}", LEGS),
    ("glued-price", "", "2024-01-02 price USD 1 " + BOM + ":A\t{{1 USD}} {T}", ""),
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
    BOM + "* " + BOM + "Assets:A\n",
    BOM + "* x\t" + BOM + "Assets:A\n",
    "$x " + BOM + "assets:A\n",
    "$x " + BOM + "1:A\n",
    "$x " + BOM + ":A\n",
    "$x " + BOM + "-:A\n",
    BOM + BOM + "Assets:A$x\n",
    BOM + "Assets:A x" + BOM + "y\n",
    BOM + BOM + "Assets:A x" + BOM + "y\n",
    BOM + ";c " + BOM + "x\n",
    BOM + "%c " + BOM + "x\n",
    "2024-01-02 *\r\n  Assets:A  1 A\r\n",
    BOM + "assets:A$x\n",
    BOM + BOM + "assets:A$x\n",
    BOM + "1:A$x\n",
    BOM + "1:A:B$c\n",
    BOM + "-:A$x\n",
    BOM + "a-b:C$x\n",
    BOM + "assets:A.b\n",
    BOM + "assets:A'b\n",
    BOM + "assets:A" + BOM + "$x\n",
    BOM + "assets:A\"x\"\n",
    BOM + "assets:A#t\n",
    BOM + "assets:A^l\n",
    BOM + "assets:A!\n",
    BOM + "assets:A@\n",
    BOM + "assets:A;c\n",
    "2024-01-02 open Assets:C USD \"BAD\"\n  kk: " + BOM + "Assets:D\n",
    "2024-01-02 open Assets:C USD \"BAD\"\n  kk: " + BOM + "assets:D\n",
    # Round 10: a BOM-led account where a price expects its amount.
    "2024-01-02 price USD 1 " + BOM + "assets:A1 1\n",
    # Round 11: a line with two differences, a glued BOM with a mid-line
    # `#+` and with a construct error main also makes, and a BOM-led
    # account line after an error line.
    "2024-01-02 *\n  " + BOM + "1:A:B  #+x#t\t{#t$x\n",
    "2024-01-02 price USD 1 " + BOM + ":A\t{1 USD}#t\n",
    "foo\n" + BOM + "assets:A " + BOM + "\n",
    # Round 12: where beancount's lexer starts an account after a BOM, and
    # where it swallows the BOM into an invalid token.
    '2024-01-02 custom "b" 1 ' + BOM + "-:A\t#t" + BOM + "a-b:C@\n",
    "x $" + BOM + "a:B\n",
    "x AB_" + BOM + "a:B\n",
    "x 1.5." + BOM + "a:B\n",
    "2024-01-02 *\n  ab:" + BOM + "a:B\n",
    "x -" + BOM + "a:B\n",
    "x 2024-01-01" + BOM + "a:B\n",
    # Round 21: a BOM glued to a posting's currency, or to a balance's
    # number, right before its price, cost or tolerance (and the same with a
    # blank before the BOM), with LF and CRLF line endings; a date alone with
    # a comment after it; and a line-start BOM before a skipped line start
    # with a BOM after it.
    *[
        line.replace("{E}", end)
        for end in ("\n", "\r\n")
        for gap in ("", " ")
        for line in [
            '2024-01-02 * "x"{E}  Assets:A  1 HOOL' + gap + BOM + tail
            + "{E}  Assets:B  -2 USD{E}"
            for tail in (
                "@ 2 USD",
                "@@ 2 USD",
                "{2 USD}",
                "{{2 USD}}",
                "{{4 USD}} @@ 5 USD",
                "~ 2 USD",
            )
        ]
        + ["2024-01-02 balance Assets:A 1.00" + gap + BOM + "~ 0.01 USD{E}"]
    ],
    "2024-01-02 ;c" + BOM + "\n2024-01-03 open Assets:C\n",
    "2024-01-02 ;" + BOM + "\n",
    "2024-01-02 open\n" + BOM + "*" + BOM + "\n",
    "2024-01-02 open\n" + BOM + "#" + BOM + "\n",
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
    tails = [(k,) for k in TAIL_TOKENS]
    tokens = {**TOKENS, **TAIL_TOKENS}
    for _, before, line, after in CONTEXTS:
        for prefix in PREFIXES.values():
            for kinds in short + long + tails:
                words = " ".join(tokens[k].format(i=i) for i, k in enumerate(kinds))
                text = (prefix + line.format(T=words)).rstrip(" ")
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


ACCOUNT_PROBE_SEED = 909931
ACCOUNT_PROBE_COUNT = 2000

# BOM-led accounts, as beancount reads them (`<BOM>` as the first character),
# with and without an account of rledger's after the BOMs.
ACCOUNT_PROBE_FORMS = [
    BOM + "Assets:A",
    BOM + "assets:A",
    BOM + "1:A",
    BOM + "1:A:B",
    BOM + ":A",
    BOM + "-:A",
    BOM + "a-b:C",
    BOM + BOM + "kk:" + BOM,
    BOM + BOM + "assets:A",
    "Heading" + BOM + "a-b:C",
    BOM + "Ü:A",
]
# What follows them, glued or after a blank.
ACCOUNT_PROBE_TAILS = [
    "$x",
    BOM + "\"s\"",
    "~" + BOM + "1:A",
    BOM + "x",
    ";c\t" + BOM + "1.5",
    "#t",
    BOM + "%",
    "{",
    ",Ü:A",
    "T#!",
    "\"x\"",
    ".b",
    "'b",
    BOM,
    "^l",
    "@",
    "!",
    "  1" + BOM + "2",
    "\t-2.5",
    BOM + "a-b:C",
]
ACCOUNT_PROBE_PREFIXES = [
    "",
    BOM,
    BOM + BOM,
    "$x ",
    BOM + "* Heading",
    BOM + "* ",
    "2024-01-02 custom \"b\" 1 ",
    "2024-01-02 *\n  ",
    "2024-01-02 *\n  kk: ",
]


def account_probe_cases():
    """A second seeded probe: a BOM-led account after each kind of line
    start, followed by one to three tails, glued to it or after a blank."""
    rng = random.Random(ACCOUNT_PROBE_SEED)
    for _ in range(ACCOUNT_PROBE_COUNT):
        text = rng.choice(ACCOUNT_PROBE_PREFIXES) + rng.choice(ACCOUNT_PROBE_FORMS)
        for _ in range(rng.choice([1, 2, 3])):
            text += rng.choice(["", "", " ", "\t"]) + rng.choice(ACCOUNT_PROBE_TAILS)
        yield HEAD + text + "\n"


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


BOM_BYTES = BOM.encode()


def later_grammar_cells(parity, is_not_syntax, src):
    """For each line, how many of beancount's errors on it after its first
    one are grammar errors (not `Invalid token`): the ones a single
    diagnostic for the line leaves out. Parsed in a forked child; None when
    beancount crashes or raises."""
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        try:
            _, errors, _ = parser.parse_string(src)
            kept = parity.keep_parse_errors(errors, is_not_syntax)
            payload = json.dumps([[line, kind] for line, kind, _ in kept])
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
    seen, later = set(), {}
    for line, kind in json.loads(payload):
        if line in seen and kind != "LexerError":
            later[line] = later.get(line, 0) + 1
        seen.add(line)
    return ",".join(f"{line}:{n}" for line, n in sorted(later.items()))


def bom_roles_in_child(src):
    """Where beancount's own lexer puts the BOMs of `src`, as byte offsets:
    the `ACCOUNT` tokens that start with a BOM (`start-end`, comma-joined),
    and the BOMs inside an invalid token past its leading BOMs (comma-joined).
    Lexed in a forked child, as the C lexer can crash; None when it does, or
    when a token cannot be placed in the source."""
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        try:
            data = src.encode()
            accounts, inner = [], []
            pos = 0
            for name, _, text, _ in lexer.lex_iter_string(src):
                if not text:
                    continue
                at = data.find(text, pos)
                if at < 0:
                    raise ValueError("token not found")
                pos = at + len(text)
                if name == "ACCOUNT" and text.startswith(BOM_BYTES):
                    accounts.append(f"{at}-{pos}")
                elif name == "error":
                    lead = len(text) - len(text.lstrip(BOM_BYTES))
                    k = text.find(BOM_BYTES, lead)
                    while k >= 0:
                        inner.append(str(at + k))
                        k = text.find(BOM_BYTES, k + len(BOM_BYTES))
            payload = json.dumps([",".join(accounts), ",".join(inner)])
        except Exception:  # the lexer raised: no verdict
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
    return json.loads(payload)


# A run of BOMs beancount reads as an account's first character: it is
# followed by an account's continuation characters, a `:` and more.
BOM_ACCOUNT = re.compile(
    "\ufeff+(?=[A-Za-z0-9\\-\u0080-\U0010ffff]*:[A-Za-z0-9\u0080-\U0010ffff])"
)


def analog(src):
    """`src` with its BOMs replaced by ordinary characters that lex alike:
    a run beancount reads into an account by `Ü` (one more account
    character there too), any other run by `$` (an invalid token's start)."""
    return re.sub("\ufeff+", "$", BOM_ACCOUNT.sub("Ü", src))


def hash_bang_analog(src):
    """`src` with each `#!` / `#+` that does not start its line made `$!` /
    `$+`, an ordinary invalid run on both sides: rledger reads a mid-line
    `#!` / `#+` as one token to the end of the line (part 2 of #2928), so
    counting this input tells whether that is a line's whole difference."""
    return re.sub(r"(?<=[^\n])#(?=[!+])", "$", src)


def alone_cells(parity, is_not_syntax, src, cache):
    """beancount's count for each line of `src` after the head, alone: after
    the head, under a bare `2024-01-02 *` header when indented (the Rust
    test's `standalone_count`). A line beancount crashes on alone is left
    out."""
    out = []
    lines = src.split("\n")
    for at in range(3, len(lines) + 1):
        text = lines[at - 1]
        if at == len(lines) and not text:
            break
        if text not in cache:
            header = TXN_BARE if text.lstrip(BOM)[:1] in (" ", "\t") else ""
            cells = counts_in_child(parity, is_not_syntax, HEAD + header + text + "\n")
            line = 4 if header else 3
            cache[text] = None if cells is None else dict(
                (int(a), int(b)) for a, b in (c.split(":") for c in cells.split(",") if c)
            ).get(line, 0)
        if cache[text] is not None:
            out.append(f"{at}:{cache[text]}")
    return ",".join(out)


def rledger_cells(binary, sources):
    """The `parse_error_lines` binary's per-line counts for each source, an
    unclosed `pushtag` / `pushmeta` at line 0 as in the parity harness."""
    frames = b"".join(
        f"{i}\n{len(s.encode())}\n".encode() + s.encode() for i, s in enumerate(sources)
    )
    out = subprocess.run([binary], input=frames, capture_output=True, check=True)
    cells = {}
    for line in out.stdout.decode().splitlines():
        result = json.loads(line)
        counts = {}
        for at, code, _ in result["errors"]:
            at = 0 if code in ("P0021", "P0023") else at
            counts[at] = counts.get(at, 0) + 1
        cells[int(result["id"])] = ",".join(
            f"{at}:{n}" for at, n in sorted(counts.items())
        )
    return [cells[i] for i in range(len(sources))]


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--main-binary",
        required=True,
        help="the parse_error_lines example built from main",
    )
    args = ap.parse_args()
    import beancount

    # The table records beancount 3.2.3's counts and token boundaries.
    if beancount.__version__ != "3.2.3":
        sys.exit(f"error: beancount {beancount.__version__}, expected 3.2.3")
    parity = load("parity", REPO / "scripts/compat-parse-error-parity.py")
    is_not_syntax = load("matrix", REPO / "scripts/stray-char-matrix.py").is_not_syntax
    seen = set()
    alone_cache = {}
    rows = []
    sources = itertools.chain(
        matrix_cases(),
        (HEAD + extra for extra in EXTRA),
        probe_cases(),
        account_probe_cases(),
    )
    for src in sources:
        if src in seen:
            continue
        seen.add(src)
        cells = counts_in_child(parity, is_not_syntax, src)
        analog_cells = counts_in_child(parity, is_not_syntax, analog(src))
        hash_bang_cells = counts_in_child(parity, is_not_syntax, hash_bang_analog(src))
        if cells is None or analog_cells is None or hash_bang_cells is None:
            print(f"left out, beancount crashed or raised: {src!r}", file=sys.stderr)
            continue
        roles = bom_roles_in_child(src)
        later = later_grammar_cells(parity, is_not_syntax, src)
        if roles is None or later is None:
            print(f"left out, beancount's lexer crashed or raised: {src!r}", file=sys.stderr)
            continue
        rows.append((src, cells, analog_cells, hash_bang_cells, alone_cells(parity, is_not_syntax, src, alone_cache), roles, later))
    main = rledger_cells(args.main_binary, [row[0] for row in rows])
    main_analog = rledger_cells(args.main_binary, [analog(row[0]) for row in rows])
    for (src, cells, analog_cells, hb, alone, (accounts, inner), later), m, ma in zip(rows, main, main_analog):
        sys.stdout.write(f"{escape(src)}\t{cells}\t{m}\t{analog_cells}\t{ma}\t{hb}\t{alone}\t{accounts}\t{inner}\t{later}\n")


if __name__ == "__main__":
    main()
