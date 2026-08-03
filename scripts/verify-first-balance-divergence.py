#!/usr/bin/env python3
"""Prove that a `first-balance-by-month` divergence is beanquery#279 and not ours.

The registry in `compat-bql-test.py` pins fixtures per-file on purpose, so it
falls behind whenever the corpus grows: 5 fixtures were pinned and 59 more had
since appeared with the identical upstream bug, all counted against rledger.
Re-run this after a corpus refresh instead of eyeballing the mismatch list.

The test is beanquery's own inconsistency. `balance` mutates a shared
accumulator when evaluated, and `FIRST.update` evaluates its operand only on a
group's first row, so later postings never reach the accumulator. Adding
`LAST(balance)` to the SELECT list forces evaluation on every row and repairs
it — which is why the same query returns different numbers depending on what
else is selected.

So: if rledger's `FIRST(balance)` equals beanquery's when `balance` is forced
to evaluate, the only difference is the skipped accumulation, and the fixture
belongs in KNOWN_PYTHON_DIVERGENCES. If it does NOT, something else is going
on and the fixture must stay surfaced — that is the case this script exists to
keep honest, because a real regression hiding among dozens of known-bad pairs
is exactly what a too-broad mask would bury.

Usage:  python3 scripts/verify-first-balance-divergence.py <file-with-fixture-names>
Writes the proven-same-cause names to /tmp/fbm_same.txt.

Run it from a checkout that has the compat corpus fetched — the fixtures under
tests/compatibility/files are downloaded, not committed, so a fresh worktree
reports every candidate as "not found". Set RLEDGER to use a binary from a
different worktree than the one holding the corpus.

Needs the third-party plugins some fixtures load (beancount_reds_plugins,
beancount_lazy_plugins); without them bean-query fails to load the ledger and
the fixture is reported inconclusive rather than same-cause.
"""
import os, re, subprocess, sys, pathlib

Q_ALONE = "SELECT year, month, FIRST(balance) WHERE account ~ '^Assets' ORDER BY year, month LIMIT 12"
Q_FORCED = "SELECT year, month, FIRST(balance), LAST(balance) WHERE account ~ '^Assets' ORDER BY year, month LIMIT 12"
RLEDGER = os.environ.get("RLEDGER", "./target/release/rledger")
# beancount emits these on stderr and still exits 0, leaving the ledger short
# of directives the fixture expects.
LOAD_ERROR = re.compile(r"Error importing|error importing|<load>:")
ROW = re.compile(r'^\s*(\d{4})\s+(\d{1,2})\s+(-?[\d,.]+)\s+([A-Z][A-Z0-9._-]*)')

def rows(text, cols=3):
    out = []
    for line in text.splitlines():
        m = ROW.match(line)
        if m:
            out.append((m.group(1), m.group(2), m.group(3).replace(',', ''), m.group(4)))
    return out

def run(cmd):
    """Return (stdout, failure) — `failure` is None on success, else a reason.

    Exit status alone is NOT enough here. beancount reports a failed plugin
    import as a load error on stderr and then exits 0 with a partially-loaded
    ledger, so the comparison silently becomes rledger-full vs beancount-
    partial. That is not evidence of anything and must not be read as a
    genuine disagreement.

    Nothing here can cause a false pin: a fixture only gets pinned when both
    sides produce rows and those rows match. The reason string exists so that
    "could not import a third-party plugin" is distinguishable from "the
    outputs genuinely disagree", which is the entire job of this script.
    """
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=180)
    if p.returncode != 0:
        tail = (p.stderr or p.stdout).strip().splitlines()
        return p.stdout, f"exit {p.returncode}: {tail[-1][:90] if tail else 'no output'}"
    for line in (p.stderr or "").splitlines():
        if LOAD_ERROR.search(line):
            return p.stdout, f"load error: {line.strip()[:90]}"
    return p.stdout, None

def find(name):
    for d in ("tests/compatibility/files", "tests/regressions"):
        hits = list(pathlib.Path(d).rglob(name))
        if hits: return str(hits[0])
    return None

with open(sys.argv[1]) as fh:
    files = [l.strip() for l in fh if l.strip()]
same, differ, err = [], [], []
for i, name in enumerate(files, 1):
    p = find(name)
    if not p:
        err.append((name, "not found")); continue
    try:
        rl_out, rl_fail = run([RLEDGER, "query", p, Q_ALONE])
        bq_out, bq_fail = run(["uv", "run", "--offline", "--with", "beancount", "--with", "beanquery",
                               "bean-query", p, Q_FORCED])
    except Exception as e:
        err.append((name, str(e)[:90])); continue
    if rl_fail or bq_fail:
        # Cause unproven, so the fixture stays surfaced rather than pinned.
        err.append((name, f"rledger {rl_fail}" if rl_fail else f"bean-query {bq_fail}"))
        continue
    rl, bq = rows(rl_out), rows(bq_out)
    if rl and bq and rl == bq:
        same.append(name)
    else:
        differ.append((name, len(rl), len(bq)))
    if i % 10 == 0:
        print(f"  ...{i}/{len(files)}", flush=True)

print(f"\n  SAME cause (rledger == beanquery-with-balance-forced): {len(same)}")
print(f"  DIFFERENT / inconclusive:                              {len(differ)}")
print(f"  errors:                                                {len(err)}")
for n, a, b in differ[:8]: print(f"    differ: {n}  (rl {a} rows, bq {b} rows)")
for n, e in err[:10]: print(f"    error:  {n}  {e}")
if differ or err:
    print("\n  Not pinned. Prove the cause before adding these to the registry;")
    print("  a mask applied on a shared query name would bury a real regression.")
with open('/tmp/fbm_same.txt', 'w') as fh:
    fh.write('\n'.join(same) + '\n')
