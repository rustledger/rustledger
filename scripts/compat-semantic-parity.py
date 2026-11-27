#!/usr/bin/env python3
"""Semantic differential: what rledger makes of a ledger against what
beancount 3.2.3 makes of it, after a FULL load.

The parse-error harness (`scripts/compat-parse-error-parity.py`) compares
where two parsers report syntax errors. This one compares the rest of the
pipeline on well-formed ledgers: booking (every method, lots by cost, date
and label, partial and total reductions, `{}` / `{{}}` / `{#}`), prices,
interpolation, tolerances and rounding, pads and balance assertions,
options and includes, and plugins. For every ledger both sides produce a
snapshot in pta-standards' format-generic schema (`ptadiff-snapshot/1`,
`tooling/differential/SNAPSHOT.md` there):

  * errors: file, line and kind of every error;
  * entries: every booked entry (interpolated amounts filled in, each
    posting's units, resolved cost, price and flag, each transaction's
    inferred tolerances), the padding and plugin-generated ones included;
  * balances: every account's final inventory, lots at cost;
  * options: `operating_currency`, the booking method, the tolerance
    options and the per-currency display precision.

Ground truth is `beancount.loader.load_file`, run by ptadiff in forked,
crash-isolated workers. rledger's side is the `semantic_snapshot` example of
`rustledger-loader`, which loads each ledger through the canonical pipeline
(`Loader::load` then `process`, as `rledger check` does) and reads every
field from the function that owns it (see its module docs).

Comparison, normalization, categorization and minimization are all
ptadiff's (`ptadiff.semantic`), at the revision the manifest pins
(`#@ptadiff-rev`). Two snapshots are compared after canonicalization
(numbers by value to 20 significant digits, unordered things sorted) and
after the format's declared normalizers (an error placed on its directive's
first line, a transaction its own side reports an error in left out, a
plugin-made location set to nowhere, beancount's `*` tolerance default
filled in). The first difference names the mismatch with ptadiff's `sem`
category key:

    field|path|kind|booking|features

where `field|path|kind` says which snapshot field differs, what in it and
in which kind of directive, `booking` is the booking method of the account
it is about (when a cost is involved), and `features` the constructs the
directive holds (`cost-empty`, `cost-total`, `price-total`, `elided`...).

rledger's DELIBERATE differences, each documented in
`docs/reference/compatibility.md`, are declared as data in
`scripts/semantic_parity_hooks.py`: representation differences are
normalized away, and a ledger whose first difference a declared deviation
explains is counted as that deviation, apart from the mismatches. So the
match rate measures only what is undecided.

Inputs (each keyed by a content id, so a duplicate counts once):

  * `gen`: ptadiff's seeded generators of well-formed beancount ledgers
    (`GENERATOR_SAMPLE`; `s3` makes multi-file ledgers), the same ledgers on
    every run for a given ptadiff revision;
  * `compat`: the downloaded compat corpus under `tests/compatibility/files`
    (`--compat-dir`), each file loaded on its own.

The manifest (`tests/baselines/semantic-parity.manifest`) pins the count of
every category key and deviation, the id of every generated ledger that
does not match, and the verdict of every compat file. `--check` fails on a
regression (a ledger pinned as matching that no longer does), on any pin
that moved (`--update` and commit, which is how parity is ratcheted), and on
a run that does not cover the pinned inputs.

    pip install "ptadiff @ git+https://github.com/rustledger/pta-standards@<rev>#subdirectory=tooling/differential"
    cargo build --release -p rustledger-loader --example semantic_snapshot
    python scripts/compat-semantic-parity.py \\
        --rledger target/release/examples/semantic_snapshot \\
        --compat-dir tests/compatibility/files --check
"""

from __future__ import annotations

import argparse
import collections
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "tests" / "baselines" / "semantic-parity.manifest"
HOOKS = ROOT / "scripts" / "semantic_parity_hooks.py"

#: The generated ledgers every run compares: `name:seed:n` each. A pinned
#: sample sized for pull-request CI; pta-standards' nightly sweep runs the
#: same generators over far more seeds.
GENERATOR_SAMPLE = ("s1:1:2500", "s2:1:2500", "s3:1:2500", "s4:1:2500")
CATEGORY_KEY = "sem"
BEANCOUNT_VERSION = "3.2.3"

ptadiff = None


def log(message):
    print(message, file=sys.stderr, flush=True)


def load_ptadiff(path=None):
    """Import `ptadiff`: from a checkout of pta-standards'
    `tooling/differential` at `path` when given, else the installed one."""
    global ptadiff
    if path:
        sys.path.insert(0, str(Path(path).resolve()))
    import ptadiff as module
    import ptadiff.formats.beancount  # noqa: F401
    import ptadiff.semantic  # noqa: F401

    ptadiff = module
    return module


def ptadiff_revision(path=None):
    """The pta-standards commit the loaded ptadiff comes from (a checkout's
    HEAD, `-dirty` when its tooling has local changes; or the commit pip
    recorded for a git install), or None."""
    if path:

        def git(*a):
            return subprocess.run(
                ["git", "-C", str(path), *a], capture_output=True, text=True, check=False
            )

        head = git("rev-parse", "HEAD")
        if head.returncode != 0:
            return None
        dirty = git("status", "--porcelain", "--", ".").stdout.strip()
        return head.stdout.strip() + ("-dirty" if dirty else "")
    import importlib.metadata

    try:
        raw = importlib.metadata.distribution("ptadiff").read_text("direct_url.json")
    except importlib.metadata.PackageNotFoundError:
        return None
    return json.loads(raw or "{}").get("vcs_info", {}).get("commit_id")


def load_hooks_module():
    spec = importlib.util.spec_from_file_location("semantic_parity_hooks", HOOKS)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def make_differ(binary, jobs):
    fmt = ptadiff.get_format("beancount")
    ptadiff.load_hooks(fmt, HOOKS)
    oracle = fmt.semantic_oracle(version=BEANCOUNT_VERSION)
    impl = ptadiff.JsonlImplementation([str(binary)], name="rledger")
    return fmt, ptadiff.semantic.SemanticDiffer(fmt, oracle, impl, key=CATEGORY_KEY, jobs=jobs)


# --------------------------------------------------------------------------
# Inputs


class Inputs:
    def __init__(self):
        #: id -> (source, label, Ledger)
        self.items = {}
        self.seen = collections.Counter()

    def add(self, source, label, ledger):
        from ptadiff.snapshot import ledger_id

        cid = ledger_id(ledger)
        self.seen[source] += 1
        self.items.setdefault(cid, (source, label, ledger))


def collect(args, fmt):
    from ptadiff.snapshot import Ledger

    inputs = Inputs()
    for spec in GENERATOR_SAMPLE:
        name, seed, n = spec.split(":")
        for led in fmt.semantic_generators[name](int(seed), int(n)):
            inputs.add("gen", spec, led)
    if args.compat_dir:
        root = Path(args.compat_dir)
        files = sorted(
            p for p in root.rglob("*") if p.is_file() and p.suffix in (".beancount", ".bean")
        )
        n = 0
        for p in files:
            try:
                text = p.read_bytes().decode("utf-8")
            except UnicodeDecodeError:
                continue
            n += 1
            # Named as CI names it, wherever the corpus was read from.
            label = "tests/compatibility/files/" + p.relative_to(root).as_posix()
            inputs.add("compat", label, Ledger(text))
        if n < args.min_compat:
            raise SystemExit(f"error: only {n} compat files under {root}; expected {args.min_compat}+")
    return inputs


# --------------------------------------------------------------------------
# Manifest


def read_baseline(path):
    """`(meta, sections)`: `meta` the `#@` lines, `sections` each `@ name`
    section's rows (tab-split)."""
    meta = {"inputs": {}}
    sections = collections.defaultdict(list)
    section = None
    if not path.exists():
        return meta, sections
    for raw in path.read_text(encoding="utf-8").splitlines():
        if raw.startswith("#@"):
            key, _, value = raw[2:].partition(" ")
            if key == "inputs":
                source, _, n = value.partition(" ")
                meta["inputs"][source] = int(n)
            else:
                meta[key] = value
        elif raw.startswith("#") or not raw.strip():
            continue
        elif raw.startswith("@ "):
            section = raw[2:].strip()
        elif section:
            sections[section].append(raw.split("\t"))
    return meta, sections


HEADER = """\
# Semantic parity baseline: rledger against beancount 3.2.3, full pipeline.
# Written by scripts/compat-semantic-parity.py --update; see its docstring.
#
# Ids are ptadiff content ids (sha256, first 12 hex digits).
# `@ categories`: count<TAB>key, mismatching ledgers per ptadiff `sem` key.
# `@ deviations`: count<TAB>name, ledgers a declared deliberate deviation
# explains (scripts/semantic_parity_hooks.py).
# `@ mismatches`: id<TAB>key, every generated ledger that does not match.
# An unlisted generated ledger is pinned as matching (or a deviation).
# `@ ledgers`: source<TAB>id<TAB>verdict<TAB>path, one row per compat file.
"""


def verdict_label(v):
    if v.status == "mismatch":
        return v.key
    if v.status == "deviation":
        return v.key
    return v.status


def write_baseline(path, inputs, verdicts, revision):
    counts = collections.Counter(
        v.key for v in verdicts.values() if v.status == "mismatch"
    )
    devs = collections.Counter(
        v.deviation for v in verdicts.values() if v.status == "deviation"
    )
    out = [HEADER]
    out.append(f"#@ptadiff-rev {revision}")
    out.append(f"#@category-key {CATEGORY_KEY}")
    out.append(f"#@generators {' '.join(GENERATOR_SAMPLE)}")
    for source in sorted(inputs.seen):
        out.append(f"#@inputs {source} {inputs.seen[source]}")
    out.append("@ categories")
    for key, n in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
        out.append(f"{n}\t{key}")
    out.append("@ deviations")
    for name, n in sorted(devs.items(), key=lambda kv: (-kv[1], kv[0])):
        out.append(f"{n}\t{name}")
    out.append("@ mismatches")
    for cid in sorted(verdicts):
        source, _, _ = inputs.items[cid]
        v = verdicts[cid]
        if source == "gen" and v.status == "mismatch":
            out.append(f"{cid}\t{v.key}")
    out.append("@ ledgers")
    rows = {}
    for cid in verdicts:
        source, label, _ = inputs.items[cid]
        if source != "gen":
            rows[cid] = (source, cid, verdict_label(verdicts[cid]), label)
    # The downloaded corpus differs between machines (CI replays a cached
    # copy, a local fetch is usually newer), so a pinned row this run did
    # not see is kept, as the parse-error manifest keeps its own.
    _, old_sections = read_baseline(path)
    for row in old_sections.get("ledgers", []):
        if len(row) == 4 and row[1] not in rows:
            rows[row[1]] = tuple(row)
    for row in sorted(rows.values(), key=lambda r: (r[3], r[1])):
        out.append("\t".join(row))
    path.write_text("\n".join(out) + "\n", encoding="utf-8")


def run_check(inputs, verdicts, meta, sections, revision, out=print):
    """`--check`: print every finding; the exit code."""
    errors = []
    if meta.get("generators") != " ".join(GENERATOR_SAMPLE):
        errors.append(f"generator sample {' '.join(GENERATOR_SAMPLE)!r}, pinned {meta.get('generators')!r}")
    if meta.get("category-key") != CATEGORY_KEY:
        errors.append(f"category key {CATEGORY_KEY!r}, pinned {meta.get('category-key')!r}")
    if revision is not None and meta.get("ptadiff-rev") != revision:
        errors.append(f"ptadiff is at {revision!r}, the manifest pins {meta.get('ptadiff-rev')!r}")
    if inputs.seen["gen"] != meta["inputs"].get("gen"):
        errors.append(f"{inputs.seen['gen']} generated ledgers, pinned {meta['inputs'].get('gen')}")
    for message in errors:
        out(f"::error::the run does not cover the pinned inputs: {message}")

    pinned_mismatch = {row[0]: row[1] for row in sections.get("mismatches", [])}
    pinned_ledger = {row[1]: row[2] for row in sections.get("ledgers", []) if len(row) >= 3}
    regressions, stale, unpinned = [], [], []
    for cid, v in sorted(verdicts.items()):
        source, label, _ = inputs.items[cid]
        now = verdict_label(v)
        if source == "gen":
            was = pinned_mismatch.get(cid)
            if v.status == "mismatch" and was is None:
                regressions.append((f"{source} {cid}", now))
            elif v.status == "mismatch" and was != now:
                stale.append((f"{source} {cid}", was, now))
            elif v.status != "mismatch" and was is not None:
                stale.append((f"{source} {cid}", was, now))
        else:
            was = pinned_ledger.get(cid)
            if was is None:
                unpinned.append((label, now, source, cid))
            elif was == now:
                continue
            elif was in ("match",) or was.startswith("deviation:"):
                if v.status == "mismatch":
                    regressions.append((label, now))
                else:
                    stale.append((label, was, now))
            else:
                stale.append((label, was, now))

    counts = collections.Counter(v.key for v in verdicts.values() if v.status == "mismatch")
    pinned_counts = {row[1]: int(row[0]) for row in sections.get("categories", [])}
    moved = [
        (k, pinned_counts.get(k, 0), counts.get(k, 0))
        for k in sorted(set(counts) | set(pinned_counts))
        if pinned_counts.get(k, 0) != counts.get(k, 0)
    ]
    devs = collections.Counter(v.deviation for v in verdicts.values() if v.status == "deviation")
    pinned_devs = {row[1]: int(row[0]) for row in sections.get("deviations", [])}
    moved += [
        (f"deviation:{k}", pinned_devs.get(k, 0), devs.get(k, 0))
        for k in sorted(set(devs) | set(pinned_devs))
        if pinned_devs.get(k, 0) != devs.get(k, 0)
    ]
    for label, now, source, cid in unpinned:
        out(f"::warning::no pin for this content ({now}): {label}")
        out(f"pin-row\t{source}\t{cid}\t{now}\t{label}")
    for label, was, now in stale:
        out(f"::error::stale pin, {was} -> {now}: {label}")
    for label, now in regressions:
        out(f"::error::regression, matched beancount (or a declared deviation) and now {now}: {label}")
    for key, was, now in moved:
        out(f"::error::stale pin, category count {was} -> {now}: {key}")
    if errors or regressions or stale or moved:
        out(
            f"FAILED: {len(regressions)} regression(s), {len(stale) + len(moved)} stale pin(s), "
            f"{len(errors)} coverage error(s)"
        )
        if not regressions:
            out(
                "Parity or the input set changed: run this script with --update and "
                "commit tests/baselines/semantic-parity.manifest."
            )
        return 1
    out(f"no regressions ({len(unpinned)} unpinned ledger(s))")
    return 0


# --------------------------------------------------------------------------
# Self-test


def self_test():
    """The comparison must call a planted difference a mismatch and an
    identical snapshot a match, so a broken classifier cannot read as
    perfect parity."""
    from ptadiff.pool import Crash
    from ptadiff.snapshot import Ledger

    fmt = ptadiff.get_format("beancount")
    ptadiff.load_hooks(fmt, HOOKS)
    oracle = fmt.semantic_oracle(version=BEANCOUNT_VERSION)
    differ = ptadiff.semantic.SemanticDiffer(fmt, oracle, None, key=CATEGORY_KEY)
    led = Ledger(
        "2024-01-01 open Assets:Cash\n"
        "2024-01-01 open Assets:Stock \"FIFO\"\n"
        "2024-01-01 open Income:Gains\n"
        "2024-01-02 * \"buy\"\n"
        "  Assets:Stock  2 HOOL {10.00 USD}\n"
        "  Assets:Cash\n"
        "2024-01-03 * \"sell\"\n"
        "  Assets:Stock  -1 HOOL {} @ 12.00 USD\n"
        "  Assets:Cash  12.00 USD\n"
        "  Income:Gains\n"
    )
    snap = oracle.snapshot([("t", led)])["t"]
    assert not isinstance(snap, Crash), snap
    failures = []

    def expect(name, impl, status, key_prefix=""):
        v = differ.judge(led, snap, impl)
        if v.status != status or not (v.key or "").startswith(key_prefix):
            failures.append(f"{name}: {v.status} {v.key!r}, expected {status} {key_prefix!r}")

    expect("identical", json.loads(json.dumps(snap)), "match")
    gains = json.loads(json.dumps(snap))
    for e in gains["entries"]:
        if e["type"] == "transaction" and e["narration"] == "sell":
            e["postings"][2]["units"]["number"] = "-2.50"
    expect("interpolated gain", gains, "mismatch", "entries|postings.units.number|transaction")
    lots = json.loads(json.dumps(snap))
    lots["balances"]["Assets:Stock"][0]["cost"]["number"] = "11.00"
    expect("lot cost", lots, "mismatch", "balances|lots|account")
    extra = json.loads(json.dumps(snap))
    extra["errors"].append({"file": "main.beancount", "line": 7, "code": "E3001", "msg": "x"})
    expect("extra error", extra, "mismatch", "errors|impl-more|impl:E3001|transaction")
    rounded = json.loads(json.dumps(snap))
    rounded["options"]["tolerance_multiplier"] = "0.50000000000000000000001"
    expect("digits past the comparison", rounded, "match")
    expect("implementation crash", "panicked: boom", "mismatch", "impl-crash|panicked")
    for f in failures:
        print(f"::error::self-test: {f}")
    print("self-test " + ("FAILED" if failures else "passed"))
    return 1 if failures else 0


# --------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--rledger", help="the semantic_snapshot example binary")
    ap.add_argument("--compat-dir", help="downloaded compat corpus")
    ap.add_argument("--min-compat", type=int, default=100)
    ap.add_argument("--baseline", type=Path, default=BASELINE)
    ap.add_argument("--ptadiff", help="a pta-standards tooling/differential checkout")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="fail on regressions")
    mode.add_argument("--update", action="store_true", help="rewrite the baseline")
    ap.add_argument("--report", type=Path, help="write the markdown report here")
    ap.add_argument("--categories-json", type=Path, help="write ptadiff's report here")
    ap.add_argument("--results", type=Path, help="write per-ledger JSONL here")
    ap.add_argument("--minimize", type=int, default=0, metavar="TOP")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    load_ptadiff(args.ptadiff)
    if args.self_test:
        return self_test()
    if not args.rledger:
        ap.error("--rledger is required")
    revision = ptadiff_revision(Path(args.ptadiff) if args.ptadiff else None)
    fmt, differ = make_differ(args.rledger, args.jobs)
    inputs = collect(args, fmt)
    log(f"comparing {len(inputs.items)} ledgers ({dict(inputs.seen)})")
    order = sorted(inputs.items)
    verdicts = differ.evaluate([(cid, inputs.items[cid][2]) for cid in order])

    from ptadiff.cluster import Member, cluster
    from ptadiff.report import build_report, render_markdown

    totals = collections.Counter(v.status for v in verdicts.values())
    by_source = collections.defaultdict(collections.Counter)
    devs = collections.Counter()
    members = []
    for cid in order:
        source, label, led = inputs.items[cid]
        v = verdicts[cid]
        by_source[source][v.status] += 1
        if v.status == "deviation":
            devs[v.deviation] += 1
        if v.status == "mismatch":
            members.append(Member(cid, v.key, led.render(fmt.main_file), source, "", led))
    clusters = cluster(members)
    for c in clusters[: args.minimize]:
        r = differ.minimize(c.shortest.payload, c.key)
        c.minimized, c.minimized_complete = r.ledger.render(fmt.main_file), r.complete
        c.features = fmt.ledger_features(r.ledger)
    report = build_report(
        clusters,
        totals,
        by_source=by_source,
        meta={
            "title": "Semantic parity: rledger against beancount 3.2.3",
            "format": "beancount",
            "key": CATEGORY_KEY,
            "oracle": {"name": "beancount", "version": differ.oracle.version()},
            "implementation": "rledger (semantic_snapshot)",
            "ptadiff-rev": revision,
            "deviations": dict(sorted(devs.items())),
        },
    )
    md = render_markdown(report, limit=40)
    judged = totals["match"] + totals["mismatch"]
    rate = 100 * totals["match"] / judged if judged else 0.0
    md += f"\nMatch rate (deviations and oracle crashes excluded): {rate:.2f}%\n"
    if args.report:
        args.report.write_text(md, encoding="utf-8")
    if args.categories_json:
        args.categories_json.write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    if args.results:
        with open(args.results, "w", encoding="utf-8") as f:
            for cid in order:
                source, label, led = inputs.items[cid]
                v = verdicts[cid]
                d = v.diff
                f.write(
                    json.dumps(
                        {
                            "id": cid,
                            "source": source,
                            "label": label,
                            "status": v.status,
                            "key": v.key,
                            **led.to_json(cid, fmt.main_file),
                            "diff": None
                            if d is None
                            else {"field": d.field, "path": d.path, "file": d.file, "line": d.line,
                                  "oracle": d.oracle, "impl": d.impl},
                        },
                        ensure_ascii=False,
                    )
                    + "\n"
                )
    print(md)
    if args.update:
        if not revision or revision.endswith("-dirty"):
            log(
                f"error: cannot pin ptadiff at {revision!r}: install it from a pta-standards "
                "commit, or pass a clean checkout with --ptadiff"
            )
            return 2
        if not args.compat_dir:
            log("error: --update needs --compat-dir: the compat rows would be stale")
            return 2
        write_baseline(args.baseline, inputs, verdicts, revision)
        log(f"wrote {args.baseline}")
        return 0
    if args.check:
        meta, sections = read_baseline(args.baseline)
        return run_check(inputs, verdicts, meta, sections, revision)
    return 0


if __name__ == "__main__":
    sys.exit(main())
