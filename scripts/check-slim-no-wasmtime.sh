#!/usr/bin/env bash
# Guard: `cargo install rustledger --no-default-features` must NOT pull
# `wasmtime` (→ `cranelift-codegen`). The slim native binary (e.g. for
# price-download only) has to build on platforms where cranelift can't compile,
# such as Termux/aarch64. Two earlier regressions (#867, then #1427) shipped
# because nothing enforced this; this ratchet keeps it from happening a third
# time. See also #1395.
set -euo pipefail

# `cargo tree -i <pkg>` exits 0 and prints the inverse tree when the package IS
# in the graph, and exits non-zero ("did not match any packages") when it is
# absent — which is exactly the state we want.
if cargo tree -p rustledger --no-default-features -i wasmtime >/tmp/slim-wasmtime.txt 2>/dev/null; then
  echo "ERROR: wasmtime is in the --no-default-features dependency tree of rustledger." >&2
  echo "A no-default build must be wasmtime/cranelift-free (#1427/#867). Offending paths:" >&2
  cat /tmp/slim-wasmtime.txt >&2
  exit 1
fi

echo "OK: the --no-default-features rustledger build is wasmtime-free."
