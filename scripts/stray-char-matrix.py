#!/usr/bin/env python3
"""Regenerate the stray-character compatibility matrix (#2802).

For each snippet in BASES, insert each character of CHARS at every byte
offset (and, after a space, the character followed by a space), parse the
result with beancount, and record whether beancount reports an error. The
output is the expectation table that
`crates/rustledger-parser/tests/stray_char_matrix.rs` checks rledger
against, without needing Python at test time.

Run it inside the compat container, which has beancount 3.2.3:

    podman run --rm -i --userns=keep-id -v "$PWD:$PWD:Z" --workdir "$PWD" \\
        rustledger-compat:latest python3 -I scripts/stray-char-matrix.py \\
        > crates/rustledger-parser/tests/data/stray_char_matrix.tsv

(`./scripts/compat-container-build.sh` builds the image once.)

Output format, one line per snippet, tab-separated:

    base  <name>  <snippet as a JSON string>  <expectations>

`<expectations>` has one character per generated case, in generation order:
`0` beancount accepts the input, `1` it reports an error, `x` excluded
because the verdict is not a syntax verdict (beancount crashed, or rejected
an option NAME, which rledger validates when it loads options rather than
when it parses). The case order is defined by `cases()` below and mirrored
by `cases()` in the Rust test; the test checks the lengths agree, so the two
cannot drift silently.

Changing BASES or CHARS here means changing them in the test too.
"""

import json
import sys

from beancount.parser import parser

BASES = [
    ("open", '2024-01-01 open Assets:A USD,EUR "FIFO"\n'),
    ("open-meta", '2024-01-01 open Assets:A\n  kk: "v"\n'),
    ("close", "2024-01-01 close Assets:A\n"),
    ("commodity", "2024-01-01 commodity USD\n"),
    ("balance", "2024-01-01 balance Assets:A 1.00 USD\n"),
    ("balance-tol", "2024-01-01 balance Assets:A 1.00 ~ 0.01 USD\n"),
    ("pad", "2024-01-01 pad Assets:A Equity:B\n"),
    ("note", '2024-01-01 note Assets:A "n" #t ^l\n'),
    ("document", '2024-01-01 document Assets:A "p.pdf"\n'),
    ("price", "2024-01-01 price HOOL 10 USD\n"),
    ("event", '2024-01-01 event "e" "v"\n'),
    ("query", '2024-01-01 query "q" "SELECT 1"\n'),
    ("custom", '2024-01-01 custom "budget" Assets:A "x" 10 USD TRUE\n'),
    ("option", 'option "title" "T"\n'),
    ("plugin", 'plugin "p" "c"\n'),
    ("include", 'include "x.beancount"\n'),
    ("pushtag", "pushtag #t\npoptag #t\n"),
    ("pushmeta", "pushmeta kk: 1\npopmeta kk:\n"),
    ("txn", '2024-01-01 * "p" "n" #t ^l\n  Assets:A  1 USD\n  Assets:B\n'),
    ("txn-cost", "2024-01-01 *\n  Assets:A  1 HOOL {2 USD} @ 3 USD\n  Assets:B\n"),
    ("txn-meta", '2024-01-01 *\n  kk: "v"\n  Assets:A  1 USD\n    pk: 2\n  Assets:B\n'),
]

CHARS = '!@?*~^$&|{}(),#%"'


def cases(base):
    """The generated inputs for one snippet, in the order the test expects."""
    out = []
    for i in range(len(base)):
        before = base[:i]
        line = before[before.rfind("\n") + 1 :]
        # Not inside a line's indentation: that changes the line's structure
        # (it is no longer an indented line), not one token of it.
        if line and line.strip(" ") == "":
            continue
        for c in CHARS:
            out.append(before + c + base[i:])
            if i > 0 and base[i - 1] == " ":
                out.append(before + c + " " + base[i:])
    return out


def verdict(src):
    try:
        _, errors, _ = parser.parse_string(src)
    except Exception:  # beancount itself crashed: no verdict to match
        return "x"
    if any("Invalid option" in str(e.message) for e in errors):
        return "x"
    return "1" if errors else "0"


def main():
    for name, base in BASES:
        _, errors, _ = parser.parse_string(base)
        if errors:
            sys.exit(f"base {name!r} itself has errors: {errors}")
        bits = "".join(verdict(src) for src in cases(base))
        print(f"base\t{name}\t{json.dumps(base)}\t{bits}")


if __name__ == "__main__":
    main()
