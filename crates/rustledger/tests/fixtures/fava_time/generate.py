"""Generate the `--time` parity table from Fava's own parser.

Regenerate with (from the repository root):

    uv run --quiet --with fava==1.30.16 python -I \
        crates/rustledger/tests/fixtures/fava_time/generate.py \
        > crates/rustledger/tests/fixtures/fava_time/table.jsonl

Each line is one case, a JSON array `[today, fye, expr, raw, window]`: a
fixed "today", a `fiscal-year-end` option value (or null for none), an
expression, and what Fava does with it:

- `raw`: what `fava.util.date.parse_date` returns, as `[begin, end]` with
  null for None, or the string "error" when it raises.
- `window`: what Fava's time filter (`TimeFilter`) accepts, as
  `[begin, end]`, or "error" when it rejects the expression (parse_date
  raised, either bound is missing, or begin is not before end).

`today` is pinned by replacing `fava.util.date.local_today`, which is the
only clock `substitute` reads, so relative forms (`year-1`, `month`, ...)
are reproducible.
"""

import datetime
import json
import random
import sys

import fava.util.date as fd

TODAYS = [
    "2026-10-20",
    "2024-02-29",
    "2023-12-31",
    "2024-01-01",
    "2025-03-31",
    "2025-04-01",
    "2021-01-03",
    "0001-01-15",
    "9999-12-15",
]

FYES = [None, "12-31", "03-31", "09-30", "02-28", "06-15", "15-31", "00-31",
        "01-31", "04-05", "02-29", "13-00", "3-31", "03-31\n", "１２-３１"]

ATOMS = [
    "", "   ", "2024", "2023", "2024-03", "2024-02-29", "2023-02-29", "2024-13",
    "2024-00", "2024-12-32", "0000", "0001", "0999", "1000", "9998", "9999",
    "9999-12", "9999-12-31", "9999-12-30", "0001-01-01", "9999-q4", "9999-q3",
    "2024-q1", "2024-q2", "2024-q3", "2024-q4", "2024-q5", "2024-q0",
    "2024-w01", "2024-w00", "2024-w1", "2024-w52", "2024-w53", "2020-w53",
    "2026-w53", "2024-w54", "2024-w99", "0999-w01", "1000-w01", "0001-w01",
    "9999-w51", "9999-w52", "9999-w53", "fy2024", "fy2024-q1", "fy2024-q2",
    "fy2024-q3", "fy2024-q4", "fy2024-q5", "fy0001", "fy0002", "fy9999",
    "fy10000", "fy", "year", "year-1", "year+1", "(year-1)", "(year)",
    "year-0", "year+0", "year-2025", "year-2026", "year-1026", "year+7973",
    "year+7974", "month", "month-1", "month+1", "month+13", "month-25",
    "(month-1)", "quarter", "quarter-1", "quarter+1", "quarter+4",
    "quarter-5", "week", "week-1", "week+1", "week+52", "week-520",
    "day", "day-1", "day+1", "day+3650", "day-739000", "day+999999999",
    "day-99999999999", "week+200000000", "fiscal_year", "fiscal_year-1",
    "fiscal_year+1", "fiscal_quarter", "fiscal_quarter-1", "fiscal_quarter+5",
    "(fiscal_quarter-4)", "today", "yesterday", "monthly", "years",
    "year - month", "month - year", "2024-01 - 2024-03", "2024-01 to 2024-03",
    "2024-01to2024-03", "2024-01-2024-03", "2024 - 2023", "2024 - 2024",
    "2020-2021-2022", "2020 - 2021 - 2022", "fy2023 - fy2024",
    "fy2023-fy2024", "2023 - fyfy2024", "2023 tofy2024", "2023 to fy2024-q2",
    "2024-01-15 - 2024-01-15", "2024-01-15 - 2024-01-16", "2024-01-15-2024-01-16",
    "  2024  ", "2024\n", "2024 -\n2025", "2024\n- 2025", "\t2024-q1",
    "\x1c2024\x1f", " 2024　", "２０２４", "٢٠٢٤", "2024-٠٣",
    "𝟐𝟎𝟐𝟒", "YEAR", "Year-1", "FY2024", "2024-Q1", "2024-W05", "TODAY",
    "garbage", "2024-1", "24", "20244", "2024-", "-2024", "to 2024",
    "2024 to", "2024 - ", "year-month", "year+month",
    "year+99999999999999999999999999999999999999999 - 2024",
    "2023 - month+99999999999999999999999999999999999999999999 - 2024",
    "2023 - year-999999999999999999999999999999999999999999999 - 2024",
    "2023 - quarter+9999999999999999999999999999999999999999999 - 2024",
    "2023 - fiscal_year+9999999999999999999999999999999999999999 - 2024",
    "2023 - week+99999999999999999999 - 2024",
    "fiscal_quarter+99999999999999999999",
    "2024 - day", "day - 2030", "year - year+1", "month-1 - month",
    "year-1to year", "fiscal_year - fiscal_year", "year-١",
    "2024-q1 - 2024-w10", "2024-w10 - 2024-q1", "fy2024-q1 - fy2024-q3",
    "2024-01 – 2024-03", "2024/01", "2024.01", "2024 01",
]

TOKENS = ["2024", "2023", "-", " - ", " to ", "to", "year", "month", "day",
          "week", "quarter", "fiscal_year", "fiscal_quarter", "-1", "+2", "(",
          ")", "fy", "-q2", "-w10", "-03", "-15", " ", "q", "w", "1999",
          "fy2020", "9999", "0000"]


def iso(d):
    return None if d is None else d.isoformat()


def run(today, fye_str, expr):
    fd.local_today = lambda: today
    fye = None if fye_str is None else fd.parse_fye_string(fye_str)
    try:
        b, e = fd.parse_date(expr, fye)
        raw = [iso(b), iso(e)]
    except Exception:  # noqa: BLE001 -- any raise is Fava rejecting it
        raw = "error"
    if raw == "error" or raw[0] is None or raw[1] is None or raw[0] >= raw[1]:
        window = "error"
    else:
        window = raw
    return raw, window


def main():
    rng = random.Random(2643)
    exprs = list(ATOMS)
    fuzz = ["".join(rng.choice(TOKENS) for _ in range(rng.randint(1, 6)))
            for _ in range(400)]
    seen = set()
    out = sys.stdout
    for today_s in TODAYS:
        today = datetime.date.fromisoformat(today_s)
        for fye_str in FYES:
            # The full expression list under the default fiscal year for every
            # day; the fiscal-year forms only under the other fiscal years.
            if fye_str is None:
                # Random token soup only under the first day: it probes the
                # range splitting and substitution order, not the calendar.
                cases = exprs + (fuzz if today_s == TODAYS[0] else [])
            else:
                pool = exprs + (fuzz if today_s == TODAYS[0] else [])
                cases = [x for x in pool if "fy" in x or "fiscal" in x] + [
                    "fiscal_year", "fiscal_quarter", "fiscal_year-1",
                    "fiscal_quarter+1", "fiscal_quarter-3", "fy2024",
                    "fy2024-q4", "fy0001", "fy9999",
                ]
            for expr in cases:
                key = (today_s, fye_str, expr)
                if key in seen:
                    continue
                seen.add(key)
                raw, window = run(today, fye_str, expr)
                out.write(json.dumps([today_s, fye_str, expr, raw, window],
                                     ensure_ascii=True,
                                     separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
