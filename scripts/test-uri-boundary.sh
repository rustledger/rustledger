#!/usr/bin/env bash
#
# Self-test for `check-uri-boundary.sh`.
#
# A grep ratchet whose regex has quietly stopped matching is worse than no
# ratchet: it reports "ok" forever and everyone believes it. This plants each
# violation the guard claims to catch and asserts it actually fails, then
# asserts the escape hatch and the test-module exemption still work.
#
# The fixture is a scratch file created and removed under
# `crates/rustledger-lsp/src/`; it is never compiled (no `mod` declares it).
#
# Usage
# -----
#   ./scripts/test-uri-boundary.sh

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

fixture="crates/rustledger-lsp/src/zz_uri_boundary_fixture.rs"
trap 'rm -f "$fixture" "crates/rustledger-lsp/tests/zz_uri_eq_fixture.rs"' EXIT

fail=0

# A clean tree must pass, or every result below is meaningless.
if ! ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
    echo "FAIL: the guard does not pass on an unmodified tree" >&2
    ./scripts/check-uri-boundary.sh || true
    exit 1
fi

# Each of these must be caught. They are the exact shapes that existed in the
# crate before `proto.rs`: assembly by format!, by literal, by push; parsing by
# prefix strip or test; and `url`'s own conversions called outside the boundary.
must_catch=(
    'fn f(p: &std::path::Path) -> String { format!("file://{}", p.display()) }'
    'fn f() -> String { "file://".to_string() }'
    'fn f(s: &mut String) { s.push_str("file://"); }'
    'fn f(u: &str) -> Option<&str> { u.strip_prefix("file://") }'
    'fn f(u: &str) -> bool { u.starts_with("file://") }'
    'fn f(u: &str) -> &str { u.trim_start_matches("file://") }'
    'fn f(p: &std::path::Path) { let _ = url::Url::from_file_path(p); }'
    'fn f(u: &url::Url) { let _ = u.to_file_path(); }'
)
for line in "${must_catch[@]}"; do
    printf '%s\n' "$line" > "$fixture"
    if ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
        echo "FAIL: not caught: $line" >&2
        fail=1
    fi
done

# The second rule: URIs compared as strings. These are the shapes that actually
# occurred — in the server's diagnostics cache and in eleven protocol tests.
uri_eq_catch=(
    'fn f(p: &P, b: &str) -> bool { p.uri.as_str() == b_uri }'
    'fn f(l: &L) -> bool { l.uri.as_str() == main_uri }'
    'fn f(u: &U) -> bool { u.as_str() == main_uri }'
    'fn f(uri: &U, o: &str) -> bool { uri.as_str() == o }'
    'fn f(a: &A) -> bool { a.uri.as_str() != b_uri }'
)
for line in "${uri_eq_catch[@]}"; do
    printf '%s\n' "$line" > "$fixture"
    if ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
        echo "FAIL: URI string comparison not caught: $line" >&2
        fail=1
    fi
done

# It must apply to tests/ too, which is where eleven of the twelve were.
test_fixture="crates/rustledger-lsp/tests/zz_uri_eq_fixture.rs"
printf '%s\n' 'fn f(p: &P) -> bool { p.uri.as_str() == bad_uri }' > "$test_fixture"
if ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
    echo "FAIL: URI string comparison in tests/ not caught" >&2
    fail=1
fi
rm -f "$test_fixture"

# A comment quoting the pattern must NOT trip it — the docs for this very rule
# have to be able to name what they ban.
printf '%s\n' '/// Never write `p.uri.as_str() == other_uri`; compare paths.' > "$fixture"
if ! ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
    echo "FAIL: a comment quoting the banned pattern was flagged" >&2
    fail=1
fi

# Its own escape hatch.
printf '%s\n' 'fn f(p: &P) -> bool { p.uri.as_str() == b_uri } // ratchet-allow: uri-string-eq self-test' > "$fixture"
if ! ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
    echo "FAIL: ratchet-allow: uri-string-eq did not suppress" >&2
    fail=1
fi

# The escape hatch must suppress a real violation.
printf '%s\n' 'fn f(u: &url::Url) { let _ = u.to_file_path(); } // ratchet-allow: uri-boundary self-test' > "$fixture"
if ! ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
    echo "FAIL: ratchet-allow did not suppress a violation" >&2
    fail=1
fi

# A trailing `#[cfg(test)] mod` is exempt: a test that simulates an editor's
# URI must build it by hand.
cat > "$fixture" <<'EOF'
fn ordinary() {}

#[cfg(test)]
mod tests {
    #[test]
    fn t() {
        let _ = format!("file://{}", "/tmp/x");
    }
}
EOF
if ! ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
    echo "FAIL: a violation inside a trailing #[cfg(test)] mod was flagged" >&2
    fail=1
fi

# ...but code BEFORE that module is still scanned, or the exemption would be a
# hole big enough to hide the whole crate in.
cat > "$fixture" <<'EOF'
fn ordinary(p: &std::path::Path) -> String { format!("file://{}", p.display()) }

#[cfg(test)]
mod tests {}
EOF
if ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
    echo "FAIL: non-test code before a #[cfg(test)] mod was not scanned" >&2
    fail=1
fi

# Production code AFTER a test module must still be scanned. The original awk
# exited at the first `#[cfg(test)] mod`, and real files have several, so the
# ratchet reported "ok" on a hand-rolled converter appended below one.
cat > "$fixture" <<'EOF'
#[cfg(test)]
mod tests {
    #[test]
    fn t() {
        let _ = format!("file://{}", "/tmp/x");
    }
}

pub fn sneaky(p: &std::path::Path) -> String { format!("file://{}", p.display()) }
EOF
if ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
    echo "FAIL: code after a #[cfg(test)] mod was not scanned" >&2
    fail=1
fi

# Two test modules, and clean code between and after them, must stay clean.
cat > "$fixture" <<'EOF'
#[cfg(test)]
mod a {
    fn x() { let _ = format!("file://{}", "/tmp/x"); }
}

pub fn between() {}

#[cfg(test)]
mod b {
    fn y() { let _ = "file:///x".strip_prefix("file://"); }
}

pub fn after() {}
EOF
if ! ./scripts/check-uri-boundary.sh >/dev/null 2>&1; then
    echo "FAIL: clean code around two test modules was flagged" >&2
    fail=1
fi

if [ "$fail" -ne 0 ]; then
    echo "self-test FAILED" >&2
    exit 1
fi

echo "ok: check-uri-boundary.sh catches all 8 conversion shapes and 6 URI-string comparisons, honors both escape hatches, and scopes the test-module exemption to the module BODY."
