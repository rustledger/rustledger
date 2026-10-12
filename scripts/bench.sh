#!/usr/bin/env bash
# Benchmark script for comparing rustledger vs other plain-text accounting tools
#
# Usage: ./scripts/bench.sh [transactions]
#   transactions: number of transactions to generate (default: 10000)
#
# Run from nix develop shell:
#   nix develop .#bench
#   ./scripts/bench.sh
#
set -euo pipefail

TRANSACTIONS=${1:-10000}
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

echo "=== Benchmark: $TRANSACTIONS transactions ==="
echo ""

# Build rustledger
echo "Building rustledger (release)..."
cargo build --release -p rustledger --no-default-features --quiet

# Generate test data
echo "Generating test ledgers..."
python3 <<EOF
import random
from datetime import date, timedelta

random.seed(42)  # Reproducible

accounts = [
    "Assets:Bank:Checking",
    "Assets:Bank:Savings",
    "Assets:Investments:Stocks",
    "Liabilities:CreditCard",
    "Expenses:Food:Groceries",
    "Expenses:Food:Restaurant",
    "Expenses:Transport:Gas",
    "Expenses:Transport:PublicTransit",
    "Expenses:Utilities:Electric",
    "Expenses:Utilities:Internet",
    "Expenses:Shopping:Clothing",
    "Expenses:Shopping:Electronics",
    "Income:Salary",
    "Income:Interest",
    "Equity:Opening-Balances",
]

transactions = []
start_date = date(2020, 1, 1)
for i in range($TRANSACTIONS):
    d = start_date + timedelta(days=i // 10)
    amount = round(random.uniform(5, 500), 2)
    expense = random.choice([a for a in accounts if a.startswith("Expenses:")])
    source = random.choice(["Assets:Bank:Checking", "Liabilities:CreditCard"])
    payee = f"Payee {i % 100}"
    narration = f"Transaction {i}"
    transactions.append((d, payee, narration, expense, source, amount))

# Write Beancount format
with open("$TMPDIR/benchmark.beancount", "w") as f:
    f.write('option "operating_currency" "USD"\n\n')
    for acc in accounts:
        f.write(f"2020-01-01 open {acc}\n")
    f.write("\n")
    for d, payee, narration, expense, source, amount in transactions:
        f.write(f'{d} * "{payee}" "{narration}"\n')
        f.write(f"  {expense}  {amount} USD\n")
        f.write(f"  {source}\n\n")

# Write Ledger/hledger format
with open("$TMPDIR/benchmark.ledger", "w") as f:
    for d, payee, narration, expense, source, amount in transactions:
        f.write(f"{d} {payee} | {narration}\n")
        f.write(f"    {expense}  \${amount:.2f}\n")
        f.write(f"    {source}\n\n")

print(f"Generated {$TRANSACTIONS} transactions")
EOF

echo ""
echo "=== Tool Versions ==="
echo "rustledger: $(./target/release/rledger --version 2>&1 || echo 'built')"
echo "beancount:  $(bean-check --version 2>&1 | head -1)"
echo "ledger:     $(ledger --version | head -1)"
echo "hledger:    $(hledger --version)"
echo ""

echo "=== Validation Benchmark (parse + check) ==="
echo "rustledger & beancount use .beancount format; ledger & hledger use .ledger format"
echo ""
hyperfine \
  --warmup 3 \
  --runs 10 \
  --export-json "$TMPDIR/validation.json" \
  --command-name 'rustledger' "./target/release/rledger check $TMPDIR/benchmark.beancount" \
  --command-name 'beancount' "bean-check $TMPDIR/benchmark.beancount" \
  --command-name 'ledger' "ledger -f $TMPDIR/benchmark.ledger accounts" \
  --command-name 'hledger' "hledger check -f $TMPDIR/benchmark.ledger"

echo ""
echo "=== Balance Report Benchmark (parse + compute) ==="
echo "All tools computing account balances on equivalent data"
echo ""
hyperfine \
  --warmup 3 \
  --runs 10 \
  --export-json "$TMPDIR/balance.json" \
  --command-name 'rustledger' "./target/release/rledger report $TMPDIR/benchmark.beancount balances > /dev/null" \
  --command-name 'beancount' "bean-query -q $TMPDIR/benchmark.beancount BALANCES > /dev/null" \
  --command-name 'ledger' "ledger -f $TMPDIR/benchmark.ledger balance > /dev/null" \
  --command-name 'hledger' "hledger -f $TMPDIR/benchmark.ledger balance > /dev/null"

echo ""
echo "=== Summary ==="
python3 <<EOF
import json

# This heredoc is unquoted, so the shell expands it: no backticks or dollar
# signs below except the TMPDIR paths.
def wall_clock(r):
    """(mean, stddev) of one result's wall-clock time, in seconds.

    hyperfine 1.x puts them at the top level ('mean', 'stddev'); 2.x moved
    them to summary.time_wall_clock (#2509). This script runs on the nix
    devshell's hyperfine, which a flake.lock update can move across that
    boundary, so it reads both. The CI workflows pin their own (#2499).
    """
    if "mean" in r:
        return r["mean"], r["stddev"]
    t = r["summary"]["time_wall_clock"]
    if t.get("unit", "second") != "second":
        raise SystemExit("unexpected hyperfine time unit %r for %r" % (t["unit"], r["command"]))
    return t["mean"], t["stddev"]

with open("$TMPDIR/validation.json") as f:
    val = json.load(f)

with open("$TMPDIR/balance.json") as f:
    bal = json.load(f)

print("Validation (parse + check):")
for r in sorted(val['results'], key=lambda x: wall_clock(x)[0]):
    mean, stddev = wall_clock(r)
    print(f"  {r['command']:12s} {mean*1000:7.1f}ms ± {stddev*1000:.1f}ms")

print("")
print("Balance report (parse + compute):")
for r in sorted(bal['results'], key=lambda x: wall_clock(x)[0]):
    mean, stddev = wall_clock(r)
    print(f"  {r['command']:12s} {mean*1000:7.1f}ms ± {stddev*1000:.1f}ms")
EOF
