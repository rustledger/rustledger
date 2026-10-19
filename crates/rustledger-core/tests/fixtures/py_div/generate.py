#!/usr/bin/env python3
"""Generate the differential fixture for `rustledger_core::py_div` (#2652).

`compound.txt.gz` does the same for `py_compound_per_unit`: rows of
`per total units expected tag`, beancount's `(total + per * |units|) / |units|`
with each step rounded to the context in turn.

Each line of `cases.txt.gz` is `a b expected`, where `expected` is what
`py_div(a, b).to_string()` must print: Python's own `decimal` division under
beancount's context (Python's default -- prec=28, ROUND_HALF_EVEN; beancount
3.2.3 never installs another for booking), written as a plain decimal
(`format(q, "f")`). The rows where a `rust_decimal::Decimal` cannot hold
Python's answer get the documented substitute instead (see `expected()` and
the `py_div` docs); each such row is tagged in the fourth column so the test
can count them.

Regenerate (stdlib only, deterministic -- the gzip has mtime 0):

    python3 crates/rustledger-core/tests/fixtures/py_div/generate.py

then run `cargo test -p rustledger-core --test py_div_differential`.
"""

import decimal
import gzip
import os
import random
from decimal import Decimal
from fractions import Fraction

# beancount's context: Python's default.
CTX = decimal.Context(
    prec=28,
    rounding=decimal.ROUND_HALF_EVEN,
    Emin=-999999,
    Emax=999999,
    traps=[decimal.InvalidOperation, decimal.DivisionByZero, decimal.Overflow],
)
assert decimal.DefaultContext.prec == 28
assert decimal.DefaultContext.rounding == decimal.ROUND_HALF_EVEN

MAX_MANTISSA = 2**96 - 1  # rust_decimal::Decimal::MAX's mantissa
MAX_SCALE = 28


def fmt(mantissa: int, scale: int) -> str:
    """Render (mantissa, scale) the way rust_decimal's Display does."""
    sign = "-" if mantissa < 0 else ""
    digits = str(abs(mantissa))
    if scale == 0:
        return sign + digits
    digits = digits.rjust(scale + 1, "0")
    return f"{sign}{digits[:-scale]}.{digits[-scale:]}"


def expected(a: str, b: str):
    da, db = Decimal(a), Decimal(b)
    if db == 0:
        return "None", "div0"
    q = CTX.divide(da, db)
    exp = q.as_tuple().exponent
    if q == 0:
        # A zero has no sign in rustledger (`negate_python`).
        q = abs(q)
        return (fmt(0, -exp) if exp < 0 else "0"), "zero"
    if exp > 0:
        # `2E+1`: same value at scale 0, or None past Decimal::MAX.
        v = int(q)
        return (str(v) if abs(v) <= MAX_MANTISSA else "None"), "posexp"
    if exp >= -MAX_SCALE:
        return format(q, "f"), "exact-repr"
    # Python keeps 28 significant digits below 1e-28: the exact quotient,
    # rounded once (half even) to 28 places -- or None if that is zero.
    scaled = Fraction(da) / Fraction(db) * 10**MAX_SCALE
    r = round(scaled)  # Fraction.__round__ is half-even
    if r == 0:
        return "None", "underflow-zero"
    return fmt(r, MAX_SCALE), "underflow"


def rand_decimal(rng, max_digits=29, scale=None):
    if scale is None:
        scale = rng.randint(0, MAX_SCALE)
    nd = rng.randint(1, max_digits)
    m = rng.randint(10 ** (nd - 1) if nd > 1 else 0, 10**nd - 1)
    m = min(m, MAX_MANTISSA)
    if rng.random() < 0.3:
        m = -m
    return fmt(m, scale)


def cases(rng):
    # 1. Every small integer pair, both signs of the divisor.
    for a in range(0, 61):
        for b in range(1, 61):
            yield str(a), str(b)
            if b % 7 == 0:
                yield str(a), str(-b)
    # 2. Small integers at every scale pairing (the ideal-exponent rule).
    for _ in range(30000):
        a = rng.randint(0, 2000)
        b = rng.randint(1, 200)
        yield fmt(a, rng.randint(0, MAX_SCALE)), fmt(b, rng.randint(0, MAX_SCALE))
    # 3. Exact quotients: a = b * q, so the remainder is zero.
    for _ in range(25000):
        q = rng.randint(1, 10 ** rng.randint(1, 14))
        b = rng.randint(1, 10 ** rng.randint(1, 14))
        if q * b > MAX_MANTISSA:
            continue
        sa = rng.randint(0, MAX_SCALE)
        sb = rng.randint(0, MAX_SCALE)
        yield fmt(q * b, sa), fmt(b, sb)
    # 4. Random operands, any digit count, any scale (mostly inexact).
    for _ in range(40000):
        yield rand_decimal(rng), rand_decimal(rng, max_digits=rng.choice([1, 2, 5, 12, 29]))
    # 4b. Random operands whose quotient Python writes at 28 places or fewer
    #     (|q| >= 0.1 or exact), so the row checks Python's own string; most
    #     random quotients below 0.1 need a 29th place no Decimal has.
    kept = 0
    while kept < 45000:
        a, b = rand_decimal(rng), rand_decimal(rng, max_digits=rng.choice([1, 2, 5, 12, 29]))
        if expected(a, b)[1] == "exact-repr":
            kept += 1
            yield a, b
    # 5. Ties at the 28th significant digit: a 29-digit exact quotient ending
    #    in 5, reached directly (b = 1) and through b = 2, 4, 5, 0.2, 2.0 ...
    for _ in range(10000):
        head = rng.randint(10**27, 10**28 - 1)
        q = head * 10 + 5  # 29 digits, ends in 5
        b_m, b_s = rng.choice([(1, 0), (2, 0), (5, 0), (4, 0), (2, 1), (20, 1), (8, 0), (25, 2)])
        a_m = q * b_m
        if a_m > MAX_MANTISSA:
            continue
        yield fmt(a_m, rng.randint(b_s, MAX_SCALE)), fmt(b_m, b_s)
    # 6. Near-ties: just above and below, via a sticky remainder.
    for _ in range(8000):
        head = rng.randint(10**27, 10**28 - 1)
        q = head * 10 + 5
        if q * 3 + 2 > MAX_MANTISSA:
            continue
        for delta in (-1, 1):
            yield fmt(q * 3 + delta, rng.randint(0, MAX_SCALE)), "3"
    # 7. Huge dividends, small divisors (positive exponent and overflow).
    for _ in range(8000):
        a = rng.randint(MAX_MANTISSA // 1000, MAX_MANTISSA)
        b = rng.randint(1, 1000)
        yield fmt(a, 0), fmt(b, rng.randint(0, 4))
    for m in (MAX_MANTISSA, MAX_MANTISSA - 1, 10**28, 10**28 - 1):
        for b in ("1", "0.5", "2", "3", "1.0", "0.1", "10", "7"):
            yield fmt(m, 0), b
    # 8. Tiny dividends, large divisors (exponent below -28, underflow to 0).
    for _ in range(8000):
        a = rng.randint(1, 10 ** rng.randint(1, 8))
        b = rng.randint(1, 10 ** rng.randint(1, 29))
        if b > MAX_MANTISSA:
            continue
        yield fmt(a, MAX_SCALE - rng.randint(0, 6)), fmt(b, rng.randint(0, 3))
    # 9. Zeros at every scale, over both signs.
    for sa in range(0, MAX_SCALE + 1):
        for b in ("4", "-4", "0.5", "3", "-0.25", "1E-28"):
            if b == "1E-28":
                b = fmt(1, 28)
            yield fmt(0, sa), b
    # 10. Division by zero.
    for a in ("1", "0", "-2.5", "0.00"):
        yield a, "0"
    # 11. The issue's ledgers.
    yield "10", "4"
    yield "10.00", "4"
    yield "10", "3"
    yield "7.5", "3"


def expected_compound(per: str, total: str, units: str):
    """beancount's `{per # total}` over `units`, in
    `booking_full.convert_costspec_to_cost`: each step rounded in turn."""
    n = abs(Decimal(units))
    if n == 0:
        return "None", "div0"
    cost_total = CTX.add(Decimal(total), CTX.multiply(Decimal(per), n))
    q = CTX.divide(cost_total, n)
    exp = q.as_tuple().exponent
    if q == 0:
        q = abs(q)
        return (fmt(0, min(-exp, MAX_SCALE)) if exp < 0 else "0"), "zero"
    if exp > 0:
        v = int(q)
        return (str(v) if abs(v) <= MAX_MANTISSA else "None"), "posexp"
    if exp >= -MAX_SCALE:
        return format(q, "f"), "exact-repr"
    r = round(Fraction(cost_total) / Fraction(n) * 10**MAX_SCALE)
    if r == 0:
        return "None", "underflow-zero"
    return fmt(r, MAX_SCALE), "underflow"


def compound_cases(rng):
    for per in range(0, 12):
        for total in range(0, 12):
            for units in range(1, 12):
                yield str(per), str(total), str(units)
    for _ in range(25000):
        per = rand_decimal(rng, max_digits=rng.choice([1, 3, 8, 15]))
        total = rand_decimal(rng, max_digits=rng.choice([1, 3, 8, 15]))
        units = rand_decimal(rng, max_digits=rng.choice([1, 2, 6, 12]))
        yield per.lstrip("-"), total.lstrip("-"), units
    # #2351: a product below 1e-28 must not vanish before the division.
    yield fmt(1, 18), "0", fmt(1, 11)
    yield "1.50", "1", "2"
    yield "1", "1", "3"
    yield "1.1", "1", "0.3"


def write_gz(path, lines):
    with open(path, "wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0, filename="") as gz:
            gz.write("".join(lines).encode())


def main():
    rng = random.Random(2652)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cases.txt.gz")
    lines = []
    for a, b in cases(rng):
        # Every operand must be a Decimal rust_decimal holds exactly.
        for s in (a, b):
            d = Decimal(s)
            t = d.as_tuple()
            mantissa = int("".join(map(str, t.digits)))
            assert 0 <= -t.exponent <= MAX_SCALE and mantissa <= MAX_MANTISSA, s
        want, tag = expected(a, b)
        lines.append(f"{a} {b} {want} {tag}\n")
    write_gz(out, lines)
    print(f"wrote {len(lines)} cases to {out}")

    out = os.path.join(os.path.dirname(out), "compound.txt.gz")
    lines = []
    for per, total, units in compound_cases(rng):
        want, tag = expected_compound(per, total, units)
        lines.append(f"{per} {total} {units} {want} {tag}\n")
    write_gz(out, lines)
    print(f"wrote {len(lines)} cases to {out}")


if __name__ == "__main__":
    main()
