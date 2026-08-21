#!/usr/bin/env python3
"""Guardrail: keep the crates.io publish list in sync with the workspace.

With `--check-registry`, also verifies every listed crate already EXISTS on
crates.io. Off by default so the per-PR run stays offline; RELEASING.md calls
it with the flag at release pre-flight.

`release-publish.yml` publishes a hand-maintained `CRATES=( ... )` array to
crates.io. If a new publishable crate is added to the workspace but not to that
array, the release silently skips it — and any crate that depends on it then
fails to publish ("failed to select a version for <crate>"). That is exactly
what broke the v0.16.0 release (rustledger-completion was missing).

Fails (exit 1) if the set of publishable workspace crates does not match the
CRATES array. Pure stdlib so it runs identically in CI and locally.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

WORKFLOW = ".github/workflows/release-publish.yml"

# crates.io rejects requests without one, with 403 — which reads as "exists"
# to a naive status check. Send a real one and treat only 404 as absent.
USER_AGENT = "rustledger release pre-flight (https://github.com/rustledger/rustledger)"

# Retried rather than treated as an answer: rate limiting and gateway errors
# say nothing about whether the crate exists.
RETRYABLE = frozenset({408, 425, 429, 500, 502, 503, 504})
ATTEMPTS = 4
BACKOFF_SECONDS = 1.5


def publishable_crates() -> set[str]:
    out = subprocess.check_output(
        ["cargo", "metadata", "--format-version", "1", "--no-deps"]
    )
    meta = json.loads(out)
    # `publish == []` means `publish = false`; anything else is publishable.
    return {p["name"] for p in meta["packages"] if p.get("publish") != []}


def listed_crates() -> set[str]:
    with open(WORKFLOW, encoding="utf-8") as f:
        text = f.read()
    m = re.search(r"CRATES=\((.*?)\)", text, re.DOTALL)
    if not m:
        sys.exit(f"::error::could not find a CRATES=( ... ) array in {WORKFLOW}")
    return set(m.group(1).split())


def unpublished(crates: set[str]) -> list[str]:
    """Which of `crates` crates.io has never seen.

    Trusted-publishing OIDC tokens cannot CREATE a crate, only push new
    versions of one that exists, so a crate that has never been published by
    hand fails the release with `403 Trusted Publishing tokens do not support
    creating new crates` — and every crate depending on it then fails with
    `no matching package`. That is v0.22.0, where `rustledger-returns` and
    `rustledger-budget` were both correctly listed in the array and neither
    had ever been published, so this script passed and the release broke
    half-way through distributing.
    """
    absent = []
    for crate in sorted(crates):
        req = urllib.request.Request(
            f"https://crates.io/api/v1/crates/{crate}",
            headers={"User-Agent": USER_AGENT},
        )
        # 404 is the answer we are here for and never retried. Everything else
        # that is not a definitive answer — rate limiting, a bad gateway, a
        # dropped connection — is retried, because failing pre-flight on a
        # transient blip would train people to ignore this check, which is
        # worse than not having it.
        last = None
        for attempt in range(ATTEMPTS):
            try:
                with urllib.request.urlopen(req, timeout=30) as resp:
                    resp.read()
                last = None
                break
            except urllib.error.HTTPError as e:
                if e.code == 404:
                    absent.append(crate)
                    last = None
                    break
                if e.code not in RETRYABLE:
                    sys.exit(f"::error::crates.io returned {e.code} for {crate}; cannot verify")
                last = f"HTTP {e.code}"
            except urllib.error.URLError as e:
                last = str(e.reason)
            if attempt + 1 < ATTEMPTS:
                time.sleep(BACKOFF_SECONDS * (2**attempt))
        if last is not None:
            sys.exit(
                f"::error::crates.io unreachable for {crate} after {ATTEMPTS} attempts "
                f"({last}); cannot verify"
            )
    return absent


def main() -> int:
    check_registry = "--check-registry" in sys.argv[1:]
    publishable = publishable_crates()
    listed = listed_crates()

    status = 0
    missing = sorted(publishable - listed)
    extra = sorted(listed - publishable)

    if missing:
        print(f"::error::Publishable crate(s) missing from the CRATES array in {WORKFLOW}:")
        for c in missing:
            print(f"  - {c}")
        print()
        print("Add each one to the array IN DEPENDENCY ORDER (dependencies before dependents).")
        print("If a crate is brand-new to crates.io, its FIRST publish must be done MANUALLY")
        print("  cargo login <token> && cargo publish -p <crate>")
        print("and trusted publishing must be configured at")
        print("  https://crates.io/crates/<crate>/settings")
        print("OIDC cannot create a crate or push to one without trusted publishing set up.")
        status = 1

    if extra:
        print(f"::error::CRATES array lists name(s) that are not publishable workspace crates:")
        for c in extra:
            print(f"  - {c}")
        print("Remove them, or fix the crate's publish setting.")
        status = 1

    if status == 0:
        print(f"✓ crates.io publish list matches all {len(publishable)} publishable crates")

    if check_registry and status == 0:
        absent = unpublished(listed)
        if absent:
            print("::error::Crate(s) in the CRATES array have never been published to crates.io:")
            for c in absent:
                print(f"  - {c}")
            print()
            print("Trusted publishing cannot create a crate. Publish each ONCE by hand:")
            print("  cargo login <token from https://crates.io/settings/tokens>")
            for c in absent:
                print(f"  cargo publish -p {c}")
            print("then configure trusted publishing at")
            for c in absent:
                print(f"  https://crates.io/crates/{c}/settings")
            print()
            print("Doing this BEFORE the release is the whole point: left until the")
            print("release runs, the crates.io job fails part-way through and every")
            print("dependent crate cascades behind it.")
            status = 1
        else:
            print(f"✓ all {len(listed)} listed crates exist on crates.io")

    return status


if __name__ == "__main__":
    raise SystemExit(main())
