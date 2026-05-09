#!/usr/bin/env bash
# Build (or rebuild) the rustledger-compat container image.
#
# Run once per machine, and again whenever `containers/compat/Containerfile`
# changes (e.g. version bumps). The dev-shell `shellHook` checks for the
# image and prints a hint if it's missing; this script is the canonical
# way to create it.
#
# The image holds beancount + beanquery + beanprice from PyPI — see the
# Containerfile for why we ship them this way instead of through nixpkgs.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
IMAGE_TAG="${RUSTLEDGER_COMPAT_IMAGE:-rustledger-compat:latest}"
CONTEXT="$REPO_ROOT/containers/compat"

if ! command -v podman >/dev/null; then
    echo "ERROR: podman not on PATH. Enter the dev shell with 'nix develop' first." >&2
    exit 1
fi

echo "Building $IMAGE_TAG from $CONTEXT/Containerfile..."
# `--no-cache` bypasses the layer cache for the `pip install` step,
# so each rebuild actually pulls latest from PyPI. The Containerfile
# is intentionally unpinned (matches CI's unpinned `pip install`);
# without `--no-cache`, podman would happily reuse a stale layer
# pinned-by-content even though the Containerfile text didn't change.
podman build --no-cache --tag "$IMAGE_TAG" "$CONTEXT"
echo ""
echo "Done. Smoke test: bean-query --version"
