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
# Scope: `crates/*/src/`, and within those files only non-test code — the BODY
# of every `#[cfg(test)] mod`, wherever it appears, is skipped, and scanning
# resumes after it. Test modules are exempt because a test simulating what an
# EDITOR sends must build the URI by hand; using our own encoder there would
# only test the encoder against itself. Integration tests live outside `src/`
# and aren't scanned by this rule. `proto.rs` itself is exempt: it is the
# implementation.
#
# (The second rule below has a WIDER scope — it also scans `crates/*/tests`
# and does not exempt test modules. See its own comment.)
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
forbidden='format!\("file://|"file://"\.to_|push_str\("file://|(strip_prefix|starts_with|trim_start_matches)\("file://|(from_file_path|to_file_path)\('

# Print a file's non-test code: every `#[cfg(test)]`-attributed `mod` BODY is
# skipped, and everything else is printed.
#
# `check-sync-primitives.sh` exits at the first such module, on the assumption
# that test modules come last. Rust does not require that, and
# `document_links.rs` alone has three — so everything after the first was
# unscanned, and appending a hand-rolled `file://` converter below it made this
# script report "ok". A ratchet with a hole where the ninth copy would go is
# worse than none, because it is believed.
#
# Braces are counted to find the end of each module rather than assuming one.
strip_test_module() {
    awk '
        # Remember a `#[cfg(test)]` so the `mod` on a following line is caught.
        /#\[cfg\(test\)\]/ { pending = 1; print; next }
        pending && /^[[:space:]]*$/ { print; next }
        pending && /^[[:space:]]*(pub[[:space:]]+)?mod[[:space:]]/ {
            pending = 0
            # A `mod foo;` declaration has no body to skip.
            if ($0 ~ /;[[:space:]]*$/) { print; next }
            depth = 0
            for (i = 1; i <= length($0); i++) {
                c = substr($0, i, 1)
                if (c == "{") depth++
                else if (c == "}") depth--
            }
            # Consume until the body closes. Blank the lines rather than
            # dropping them so grep -n line numbers stay true to the file.
            while (depth > 0 && (getline line) > 0) {
                for (i = 1; i <= length(line); i++) {
                    c = substr(line, i, 1)
                    if (c == "{") depth++
                    else if (c == "}") depth--
                }
                print ""
            }
            print ""
            next
        }
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

# A SECOND rule, over `src/` AND `tests/`: never compare URIs as strings.
#
# One file has many URI spellings, so a string comparison answers "did these two
# producers happen to spell it the same way", not "are these the same file". It
# is the defect the diagnostics cache had (a `didClose` in the client's spelling
# could not evict an entry stored in ours), and eleven more instances were then
# found in the protocol tests, where the server's URI comes from the loader's
# canonicalized path and the test's from the temp dir it made. On Linux those
# are the same string; on Windows they are not, so every one of those
# assertions silently never matched.
#
# `tests/` is in scope here, unlike the rule above: building a URI by hand is
# legitimate in a test simulating an editor, but comparing two of them as
# strings is wrong wherever it appears. Convert both sides with `uri_to_path`
# and compare paths.
#
# KNOWN GAP, stated rather than papered over: this matches on the NAME, so it
# needs one side to be called `uri`/`*_uri` or to be a `.uri` field. It caught
# all twelve real instances and every realistic variant, but
# `let a = some_uri(); a.as_str() == b` slips through. Banning every
# `.as_str() ==` in the crate would close it at the cost of one unrelated line
# today and a tax on every string comparison later; that trade is available if
# this ever misses something real.
uri_eq='\.as_str\(\) *[=!]= *[&]?[a-z_]*uri|uri\.as_str\(\) *[=!]='

uri_eq_violations=""
while IFS= read -r f; do
    # Comment-only lines are skipped: the doc comments explaining this rule
    # necessarily quote the pattern it bans.
    hits="$(grep -nE "$uri_eq" "$f" \
        | grep -vE '^[0-9]+:[[:space:]]*(//|/\*|\*)' \
        | grep -v 'ratchet-allow: uri-string-eq' || true)"
    if [ -n "$hits" ]; then
        uri_eq_violations+="$f:"$'\n'"$(printf '%s\n' "$hits" | sed 's/^/    /')"$'\n'
    fi
done < <(grep -rlE "$uri_eq" crates/*/src crates/*/tests --include='*.rs' 2>/dev/null | sort)

if [ -n "$uri_eq_violations" ]; then
    echo "error: URIs compared as strings." >&2
    echo "       A Uri is a string and a string is not a file identity: %2E vs ., a" >&2
    echo "       dot segment, C: vs c:, and a canonicalized vs an uncanonicalized" >&2
    echo "       parent all spell one file differently." >&2
    echo "       Convert both sides with uri_to_path and compare the paths." >&2
    echo "       In rustledger-lsp's protocol tests, the harness's \`same_file\`" >&2
    echo "       already does this." >&2
    echo "       If a literal string comparison is genuinely what you mean, append" >&2
    echo "         // ratchet-allow: uri-string-eq <reason>" >&2
    echo "       to the line." >&2
    echo >&2
    printf '%s' "$uri_eq_violations" >&2
    exit 1
fi

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

echo "ok: file: URI conversion confined to $boundary, and no URI compared as a string."
