#!/usr/bin/env python3
"""Generate the 1M-transaction journal used to measure memory for #2742.

Usage:

    python3 scripts/gen-hledger-perf-journal.py [transactions] [--meta] > journal.beancount

The shape approximates the counts of hledger's `tools/generatejournal 1000000
1000 10`, as used on hledger.org/PERFORMANCE.html (the benchmark #2742
answers): one transaction a day, 1000 accounts nested up to 10 levels deep,
26 commodities, two postings per transaction, two transactions in three
carrying a price annotation (`@` or `@@`), and one `price` directive per
transaction. It is not byte-comparable with hledger's output: every amount is
`1` (hledger uses the transaction number), prices are in `USD` (hledger uses
the next of its single-letter commodities, so this file has 27 commodities),
each `price` directive is in its transaction's commodity (hledger writes
`A -> B` rates), the rate cycle is 61 transactions (hledger: 60), and the
accounts share `L1..Lk` parents with a unique leaf (hledger nests chains whose
prefixes are accounts too). That is close enough for the memory analysis.
hledger is not needed: this writes beancount directly, deterministically, so a
measurement can be repeated byte for byte.

`--meta` adds what the synthetic journal leaves out and real ledgers have: a
comment line before every transaction, two metadata lines on each transaction
and one on each posting.

The output loads cleanly (`rledger check` reports no errors).
"""

from __future__ import annotations

import datetime
import sys

ACCOUNTS = 1000
DEPTH = 10
COMMODITIES = [f"C{chr(ord('A') + i)}" for i in range(26)]


def account(i: int) -> str:
    depth = 1 + i % DEPTH
    return "Assets:" + ":".join([f"L{k}" for k in range(1, depth)] + [f"A{i}"])


def main(argv: list[str]) -> int:
    meta = "--meta" in argv
    args = [a for a in argv if a != "--meta"]
    n = int(args[0]) if args else 1_000_000
    accounts = [account(i) for i in range(ACCOUNTS)]
    out = sys.stdout
    write = out.write
    write('option "title" "hledger PERFORMANCE shape (#2742)"\n\n')
    for a in accounts:
        write(f"1999-12-31 open {a}\n")
    write("\n")
    day = datetime.date(2000, 1, 1)
    one = datetime.timedelta(days=1)
    for j in range(1, n + 1):
        d = day.isoformat()
        a1 = accounts[(2 * j) % ACCOUNTS]
        a2 = accounts[(2 * j + 1) % ACCOUNTS]
        cur = COMMODITIES[(j - 1) % 26]
        rate = f"{0.70 + 0.01 * ((j - 1) % 61):.2f}"
        form = (j - 1) % 3
        if meta:
            write(f"; transaction {j}\n")
        write(f'{d} * "transaction {j}"\n')
        if meta:
            write(f'  note: "generated {j}"\n')
            write(f'  ref: "R{j}"\n')
        if form == 0:
            write(f"  {a1}  1 USD\n")
            if meta:
                write('    memo: "in"\n')
            write(f"  {a2}  -1 USD\n")
        else:
            op = "@" if form == 1 else "@@"
            write(f"  {a1}  1 {cur} {op} {rate} USD\n")
            if meta:
                write('    memo: "in"\n')
            write(f"  {a2}  -{rate} USD\n")
        if meta:
            write('    memo: "out"\n')
        write(f"{d} price {cur} {rate} USD\n\n")
        day += one
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
