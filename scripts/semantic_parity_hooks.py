"""rledger's DELIBERATE semantic differences from beancount 3.2.3, declared
as data for pta-standards' semantic differential (`ptadiff.semantic`).

Loaded by `scripts/compat-semantic-parity.py`, and by ptadiff itself with
`python -m ptadiff run --semantic ... --hooks scripts/semantic_parity_hooks.py`.

Two kinds of declaration (see `ptadiff.pipeline.load_hooks`):

* `normalize_impl_snapshot` / `normalize_oracle_snapshot`: a REPRESENTATION
  difference, where both sides mean the same and say it differently. The
  snapshot is rewritten so the difference is not seen at all.
* `DEVIATIONS`: a SEMANTIC difference rledger makes on purpose, each with
  the section of `docs/reference/compatibility.md` that documents it. A
  ledger whose first difference one of them explains is counted as that
  deviation, apart from the mismatches, so the metric measures only what
  is not decided. A predicate is narrow on purpose: it must not swallow a
  bug that happens to share a ledger with a deliberate difference.

Every entry here must name its documentation. A difference that has none
is not deliberate yet: it is a mismatch, and it stays in the metric.
"""

from __future__ import annotations

import re
from decimal import Decimal, InvalidOperation

from ptadiff.semantic import Deviation

COMPAT = "docs/reference/compatibility.md"


# -- representation ------------------------------------------------------------


#: Known Difference 3 (Push/Pop Meta and Tag Validation): an unpopped
#: `pushtag` / `pushmeta` is reported by beancount at the end of the file
#: (`<load>:0`), by rledger on the push's own line.
UNPOPPED_PUSH = frozenset({"P0021", "P0023"})

#: A missing include (`E0001`) and a document root that does not exist
#: (`E7006`): rledger reports each on the `include` or `option "documents"`
#: line that names it, beancount nowhere (`<load>:0`, or its file at line
#: 0). Same finding; the place is placed where beancount places it.
LOCATED_LOAD_ERRORS = frozenset({"E0001", "E7006"})


#: Plugin Differences, `effective_date`: beancount's plugin links a moved
#: entry `edate-<yymmdd>-<three random letters>`, rledger's
#: `edate-<yymmdd>-<n>`, deterministic. The suffix is compared as one.
_EDATE_LINK = re.compile(r"^(edate-\d{6}-)\w+$")


def _edate_links(snap: dict) -> dict:
    entries = []
    for e in snap["entries"]:
        links = e.get("links")
        if links and any(_EDATE_LINK.match(x) for x in links):
            e = {**e, "links": [_EDATE_LINK.sub(r"\1*", x) for x in links]}
        entries.append(e)
    return {**snap, "entries": entries}


def normalize_oracle_snapshot(ledger, snap: dict) -> dict:
    """The `effective_date` link suffix (`_EDATE_LINK`)."""
    return _edate_links(snap)


def normalize_impl_snapshot(ledger, snap: dict) -> dict:
    """Two representation differences of rledger's errors:

    * Known Difference 1 (Multi-Currency Transactions): beancount gives an
      unbalanced transaction ONE error listing every residual, rledger one
      `E3001` per unbalanced currency, on the same line. Same finding, so
      the `E3001`s of one line count once.
    * Known Difference 3: an unpopped push is placed where beancount places
      it, nowhere (`UNPOPPED_PUSH`); so are a missing include and a missing
      document root (`LOCATED_LOAD_ERRORS`).

    And the `effective_date` link suffix, as on the oracle's side."""
    seen: set[tuple[str, int]] = set()
    errors = []
    for e in snap["errors"]:
        if e["code"] == "E3001":
            where = (e["file"], e["line"])
            if where in seen:
                continue
            seen.add(where)
        if e["code"] in UNPOPPED_PUSH | LOCATED_LOAD_ERRORS:
            e = {**e, "file": "", "line": 0}
        errors.append(e)
    return _edate_links({**snap, "errors": errors})


# -- deliberate semantics ---------------------------------------------------------


def _oracle_msgs(m) -> list[str]:
    return [e["msg"] for e in m.oracle["errors"]]


def _average_accounts(m) -> set[str]:
    out = {
        e["account"]
        for e in m.oracle["entries"]
        if e.get("type") == "open" and e.get("booking") == "AVERAGE"
    }
    if (m.oracle.get("options") or {}).get("booking_method") == "AVERAGE":
        out |= set(m.oracle["balances"]) | set(m.impl["balances"])
        for e in m.oracle["entries"]:
            if e.get("type") == "open" and not e.get("booking"):
                out.add(e["account"])
    return out


def _average(m) -> bool:
    """Known Difference 20: beancount implements neither AVERAGE booking nor
    cost merging (`{*}`). A reduction from an AVERAGE account fails there
    (`AVERAGE method is not supported`) and the refused entry's effects
    cascade; rledger books it at the pool's average cost and presents an
    AVERAGE account as its pools. Explains a ledger where beancount refuses
    an AVERAGE or merge reduction, or whose first difference is about an
    AVERAGE account's holdings."""
    if any(
        "AVERAGE method is not supported" in msg or "Cost merging is not supported" in msg
        for msg in _oracle_msgs(m)
    ):
        return True
    d = m.diff
    averaged = _average_accounts(m)
    if d.field == "balances" and d.subject in averaged:
        return True
    return d.field == "entries" and d.subject in averaged


_RESIDUAL = re.compile(r"does not balance: \(([^)]*)\)")


def _tiny_total_price_residual(m) -> bool:
    """Known Difference 18: beancount divides an `@@` total into a per-unit
    price rounded to 28 digits and multiplies it back, leaving a residual
    like `-0.0000000000000000000000001 USD` on a total that does not divide
    evenly; rledger weighs the total as written. Explains a ledger whose
    first difference is an unbalanced-transaction error only beancount
    reports, every residual of which is below 1e-20, on a transaction with
    an `@@` price."""
    d = m.diff
    if d.field != "errors" or d.path != "impl-fewer":
        return False
    for e in d.oracle or ():
        match = _RESIDUAL.search(e["msg"])
        if not match:
            return False
        for part in match.group(1).split(","):
            number = part.strip().split(" ")[0]
            try:
                if abs(Decimal(number)) >= Decimal("1e-20"):
                    return False
            except InvalidOperation:
                return False
    text = m.text_of(d.file)
    lines = text.split("\n")[d.line - 1 : d.line + 12]
    return any("@@" in ln for ln in lines)


def _cost_currency_categorize(m) -> bool:
    """Known Difference 17: a cost spec with no currency (`{}`) whose
    currency beancount's categorization cannot resolve fails there (`Failed
    to categorize posting`), and rledger books it with the currency it
    infers. Explains a ledger whose first difference is that error, which
    only beancount reports."""
    d = m.diff
    return (
        d.field == "errors"
        and d.path == "impl-fewer"
        and all("categorize" in e["msg"] for e in d.oracle or ())
    )


_TXN_DATE = re.compile(r"^(\d{4}-\d\d-\d\d)[ \t]+(?:[*!&#?%PSTCURM]|txn)(?=[ \t]|$)", re.M)


def _same_date_across_files(m) -> bool:
    """Known Difference 7 (Cross-File Booking Order): directives sharing a
    date keep include order in rledger, where beancount compares line
    numbers taken from different files; a sale and the purchase it sells
    from, or two lots a sale chooses between, then come in a different
    order. Explains a multi-file ledger whose first difference is in a
    booked posting's cost or units, a lot-level balance, or an error on a
    transaction holding a cost spec, when two files hold transactions of
    one date."""
    if not m.ledger.files:
        return False
    texts = {m.main: m.ledger.text, **m.ledger.files}
    dates: dict[str, set[str]] = {}
    for path, text in texts.items():
        for date in _TXN_DATE.findall(text):
            dates.setdefault(date, set()).add(path)
    if not any(len(files) > 1 for files in dates.values()):
        return False
    d = m.diff
    if d.field == "errors":
        text = m.text_of(d.file)
        lines = text.split("\n")[max(d.line - 1, 0) : d.line + 12]
        body = []
        for n, line in enumerate(lines):
            if n and not line.startswith((" ", "\t")):
                break
            body.append(line)
        return d.line > 0 and any("{" in line for line in body)
    return (d.field == "entries" and d.path.startswith(("postings.cost", "postings.units"))) or (
        d.field == "balances" and d.path in ("lots", "units")
    )


_PLUGIN = re.compile(r'^plugin[ \t]+("[^"]*")(?:[ \t]+("[^"]*"))?', re.M)


def _included_file_plugins(m) -> bool:
    """Known Difference 21 (Plugins Declared in Included Files): beancount
    3.2.3 runs the plugins of the top-level file only and ignores a
    `plugin` an included file declares; rledger runs an included file's
    plugins too, each distinct plugin once, from the first file that
    declares it (`rustledger_loader::plugins_in_run_order`). Explains any
    difference in a ledger where an included file declares a plugin the
    main file does not: the two tools run different plugins over it."""
    main = set(_PLUGIN.findall(m.ledger.text))
    return any(
        set(_PLUGIN.findall(text)) - main for text in m.ledger.files.values()
    )


def _currency_accounts_order(m) -> bool:
    """Plugin Differences, `currency_accounts`: rledger appends the
    neutralizing postings after the written ones, where beancount moves
    each currency group's postings together ahead of its neutralizer. Same
    postings, same amounts. Explains a ledger running that plugin whose
    first difference is only the order of a transaction's postings."""
    return m.diff.path == "postings.order" and any(
        "currency_accounts" in plugin for plugin, _ in _PLUGIN.findall(m.ledger.text)
    )


_CUSTOM_AMOUNT = re.compile(r"^\d{4}-\d\d-\d\d[ \t]+custom\b.*\d[ \t]+[A-Z][A-Z0-9'._-]*", re.M)


def _custom_display_precision(m) -> bool:
    """Known Difference 5 (BQL Display Precision): an amount in a `custom`
    directive does not inform rledger's display precision (a budget line's
    scale is a choice about the declaration; see
    `DisplayContext::from_directives`), where beancount's parser counts it.
    Explains a ledger with an amount in a `custom` directive whose first
    difference is the display precision."""
    return m.diff.field == "options" and m.diff.path == "display_precision" and any(
        _CUSTOM_AMOUNT.search(text) for text in (m.ledger.text, *m.ledger.files.values())
    )


DEVIATIONS = [
    Deviation(
        "custom-display-precision",
        f"{COMPAT} #5 (BQL Display Precision)",
        _custom_display_precision,
        "a custom directive's amounts do not inform display precision",
    ),
    Deviation(
        "included-file-plugins",
        f"{COMPAT} #21 (Plugins Declared in Included Files)",
        _included_file_plugins,
        "an included file's plugins run too, each once",
    ),
    Deviation(
        "currency-accounts-posting-order",
        f"{COMPAT} Plugin Differences (The `currency_accounts` Plugin)",
        _currency_accounts_order,
        "neutralizing postings appended after the written ones",
    ),
    Deviation(
        "average-booking",
        f"{COMPAT} #20 (AVERAGE Booking and Cost Merging); ADR 0007",
        _average,
        "AVERAGE booking and {*} merging, which beancount does not implement",
    ),
    Deviation(
        "total-price-residual",
        f"{COMPAT} #18 (Total Prices That Do Not Divide Evenly)",
        _tiny_total_price_residual,
        "an @@ total weighed as written, not as a rounded per-unit price",
    ),
    Deviation(
        "cost-currency-categorize",
        f"{COMPAT} #17 (Cost Currencies Beancount Refuses to Categorize)",
        _cost_currency_categorize,
        "a {} cost's currency inferred where beancount cannot categorize it",
    ),
    Deviation(
        "cross-file-booking-order",
        f"{COMPAT} #7 (Cross-File Booking Order)",
        _same_date_across_files,
        "same-date directives across files kept in include order",
    ),
]
