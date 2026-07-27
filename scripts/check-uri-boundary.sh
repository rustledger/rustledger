#!/usr/bin/env bash
#
# Keep `file:` URI <-> path conversion inside `rustledger-lsp/src/proto.rs`.
#
# Four separate hand-rolled converters existed at once in this crate, and each
# was wrong in its own way: one escaped nothing, one escaped only spaces, one
# stripped the `file://` prefix without decoding it (so the URI for a path
# with a space kept the literal `%20`, naming a file that does not exist), and
# one escaped a Windows
# path separator into `%5C`. They agreed on every ASCII-only path a developer
# tests with, which is why all four survived review. `proto.rs` is now the one
# place that knows the encoding, and this is the ratchet that keeps a fifth
# copy from appearing the next time a call site needs a URI in a hurry.
#
# This is the same lightweight, named-CI-status pattern as
# `check-sync-primitives.sh` — deliberately a grep ratchet rather than a
# `dylint` lint so it needs no extra (nightly) toolchain.
#
# Scope: `crates/*/src/` only, and within those files only non-test code —
# a trailing `#[cfg(test)] mod ...` block is skipped, because a test that
# simulates what an EDITOR sends must build the URI by hand; using our own
# encoder there would only test the encoder against itself. Integration tests
# live outside `src/` and aren't scanned. `proto.rs` itself is exempt: it is
# the implementation.
#
# Escape hatch: append `// ratchet-allow: uri-boundary <reason>` to the line.
#
# Exit codes
# ----------
#   0  no URI assembly or parsing outside the boundary module
#   1  one or more violations found
#
# Usage
# -----
#   ./scripts/check-uri-boundary.sh

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

boundary="crates/rustledger-lsp/src/proto.rs"

# Two families:
#   * assembling a URI from a string ("file://" appearing in a format!, a
#     literal conversion, or a push onto a buffer), and
#   * taking one apart by hand (prefix strip/test).
# Plus `url`'s own path conversions, so `proto` stays their only caller —
# they are correct primitives, but calling them elsewhere re-creates the
# WHATWG-vs-RFC-3986 encoding gap that `proto::path_to_uri` closes.
forbidden='(format!\("file://|"file://"\.to_|push_str\("file://|(strip_prefix|starts_with|trim_start_matches)\("file://|(from_file_path|to_file_path)\()'

# Print a file's non-test code: everything up to the trailing
# `#[cfg(test)]`-attributed `mod`. Matches `check-sync-primitives.sh`.
strip_test_module() {
    awk '
        /#\[cfg\(test\)\]/ { pending = 1; print; next }
        pending && /^[[:space:]]*$/ { print; next }
        pending && /^[[:space:]]*(pub[[:space:]]+)?mod[[:space:]]/ { exit }
        { pending = 0; print }
    ' "$1"
}

violations=""
while IFS= read -r f; do
    [ "$f" = "$boundary" ] && continue
    hits="$(strip_test_module "$f" | grep -nE "$forbidden" | grep -v 'ratchet-allow: uri-boundary' || true)"
    if [ -n "$hits" ]; then
        violations+="$f:"$'\n'"$(printf '%s\n' "$hits" | sed 's/^/    /')"$'\n'
    fi
done < <(grep -rlE "$forbidden" crates/*/src --include='*.rs' 2>/dev/null | sort)

if [ -n "$violations" ]; then
    echo "error: file: URI assembled or parsed outside the boundary module." >&2
    echo "       Use rustledger_lsp::{path_to_uri, uri_to_path} (crates/rustledger-lsp/src/proto.rs)." >&2
    echo "       Hand-rolled conversions have been wrong four times: percent-encoding," >&2
    echo "       percent-decoding, and the Windows path separator each got missed." >&2
    echo "       If a raw conversion is genuinely required, append" >&2
    echo "         // ratchet-allow: uri-boundary <reason>" >&2
    echo "       to the line." >&2
    echo >&2
    printf '%s' "$violations" >&2
    exit 1
fi

echo "ok: file: URI conversion confined to $boundary."
