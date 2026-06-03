#!/usr/bin/env bash
# Ad-hoc verification that balance lenses ship fully-resolved on the
# initial `textDocument/codeLens` response, defeating the nvim resolve-
# cancellation race that surfaced as issues #1245 and #1253.
#
# This script:
#   1. Builds rledger-lsp (release-equivalent debug for speed)
#   2. Pipes a hand-crafted LSP initialize + didOpen + codeLens session
#      to its stdin
#   3. Sends a `$/cancelRequest` for the codeLens request id, mirroring
#      the nvim client behavior visible in #1253's LSP log
#   4. Parses the responses and exits non-zero unless:
#        - the codeLens response carries a balance lens with a final ✓ or ⚠
#          title (no "(checking…)" placeholder, no command:None)
#        - the lens has no `data` payload (no resolve round-trip required)
#
# A full Rust integration harness is the right next step (see the
# discussion on #1253); this script is the smaller, faster check that
# can run from a developer's shell and from CI as a one-off.
#
# Usage: bash scripts/lsp-cancel-race-repro.sh

set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

echo ">> Building rledger-lsp..."
cargo build --quiet -p rustledger-lsp --bin rledger-lsp

BIN="$ROOT/target/debug/rledger-lsp"
[[ -x "$BIN" ]] || {
    echo "ERROR: rledger-lsp binary not found at $BIN" >&2
    exit 1
}

# The exact reproduction from issue #1253. The balance assertion is valid:
# the 02-01 transaction posts 1000 USD, so the 02-02 balance check passes.
FIXTURE='2012-01-01 open Assets:Bank
2012-01-01 open Income:Employment

2012-02-01 * "Salary"
  Assets:Bank                   1000 USD
  Income:Employment

2012-02-02 balance Assets:Bank  1000 USD
'

# Helper: emit an LSP message with the proper `Content-Length` header.
emit() {
    local body="$1"
    printf 'Content-Length: %d\r\n\r\n%s' "${#body}" "$body"
}

# Build the message stream:
#   1. initialize
#   2. initialized notification
#   3. textDocument/didOpen
#   4. textDocument/codeLens (id 100)
#   5. $/cancelRequest for id 100 (the nvim race we want to defeat)
#   6. shutdown
#   7. exit notification
#
# The escaped-newline-laden didOpen payload is required because the LSP
# JSON wants the full source as a single string literal.
DIDOPEN_TEXT=${FIXTURE//$'\n'/\\n}
DIDOPEN_TEXT=${DIDOPEN_TEXT//\"/\\\"}

REQUESTS=""
REQUESTS+=$(emit '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"processId":null,"rootUri":null,"capabilities":{}}}')
REQUESTS+=$(emit '{"jsonrpc":"2.0","method":"initialized","params":{}}')
REQUESTS+=$(emit "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{\"uri\":\"file:///repro.beancount\",\"languageId\":\"beancount\",\"version\":1,\"text\":\"${DIDOPEN_TEXT}\"}}}")
REQUESTS+=$(emit '{"jsonrpc":"2.0","id":100,"method":"textDocument/codeLens","params":{"textDocument":{"uri":"file:///repro.beancount"}}}')
REQUESTS+=$(emit '{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":100}}')
REQUESTS+=$(emit '{"jsonrpc":"2.0","id":999,"method":"shutdown"}')
REQUESTS+=$(emit '{"jsonrpc":"2.0","method":"exit"}')

# Run the session. The server may respond to the codeLens request even
# after the cancel arrives (the race we are explicitly checking is OK on
# our side: we ship resolved on the initial response, no round-trip).
echo ">> Driving rledger-lsp..."
RESPONSE=$(printf '%s' "$REQUESTS" | "$BIN" 2>/dev/null || true)

# The codeLens response is one of the JSON messages in the framed
# stream. Extract the body of the id=100 response and inspect it.
# We use python because portable shell JSON parsing is misery.
RESULT=$(printf '%s' "$RESPONSE" | python3 -c '
import sys, json, re

raw = sys.stdin.buffer.read()
# Framed messages: "Content-Length: N\r\n\r\n<N bytes of JSON>"
i = 0
codelens_response = None
while i < len(raw):
    m = re.match(rb"Content-Length: (\d+)\r\n\r\n", raw[i:])
    if not m:
        i += 1
        continue
    n = int(m.group(1))
    body_start = i + m.end()
    body = raw[body_start:body_start + n]
    i = body_start + n
    try:
        msg = json.loads(body)
    except Exception:
        continue
    if msg.get("id") == 100 and "result" in msg:
        codelens_response = msg
        break

if codelens_response is None:
    print("FAIL: no codeLens response with id 100 (server dropped the request?)")
    sys.exit(1)

lenses = codelens_response["result"] or []
balance_lens = next(
    (l for l in lenses if (l.get("command") or {}).get("title", "").startswith("Balance:")
                       or (l.get("command") or {}).get("title", "").startswith(("✓", "⚠"))),
    None,
)

if balance_lens is None:
    print(f"FAIL: no balance lens in response. lenses = {lenses}")
    sys.exit(1)

cmd = balance_lens.get("command") or {}
title = cmd.get("title", "")
data = balance_lens.get("data")

if "(checking" in title:
    print(f"FAIL (issue #1253 regression): balance lens shipped with the `(checking)` placeholder. title = {title!r}")
    sys.exit(1)
if "✓" not in title and "⚠" not in title:
    print(f"FAIL: balance lens did not ship with a ✓ or ⚠ status marker. title = {title!r}")
    sys.exit(1)
if data is not None:
    print(f"FAIL: balance lens carries a resolve-data payload, exposing it to the resolve race. data = {data!r}")
    sys.exit(1)

print(f"OK: balance lens shipped fully-resolved. title = {title!r}")
') || {
    echo "$RESULT" >&2
    exit 1
}

echo "$RESULT"
