#!/usr/bin/env bash
# Shared dispatcher for compat-tool wrappers.
#
# Each wrapper (bean-query, bean-check, bean-price, ...) is a symlink
# pointing here. We dispatch by `basename "$0"` and exec podman with
# the host paths mounted at the same locations inside the container,
# so absolute paths the user passes on the command line resolve
# transparently.
#
# Mounted (preserving host paths so absolute references just work):
#   - $PWD  (cwd; also set as --workdir)
#   - $HOME (user data — beancount files, bean-price caches, etc.)
#   - /tmp  (test infrastructure; cargo+tempfile create temp files
#           under /tmp/nix-shell.../*.beancount and pass absolute paths)
#
# `--userns=keep-id`: map host UID into the container so writes
#                     (bean-format -w, bean-price cache) end up
#                     host-owned at the right perms.
# `--rm`: don't leave a stopped container per invocation.
# `-i`: forward stdin (some tools accept ledger text on stdin).

set -euo pipefail

TOOL="$(basename "$0")"
IMAGE_TAG="${RUSTLEDGER_COMPAT_IMAGE:-rustledger-compat:latest}"

if ! podman image exists "$IMAGE_TAG" 2>/dev/null; then
    cat >&2 <<EOF
ERROR: rustledger-compat image not built.
Run once: ./scripts/compat-container-build.sh
EOF
    exit 1
fi

# Build the volume list. Each `-v src:dst:Z` mounts `src` at `dst`
# (same path) and applies SELinux relabeling on systems that need it
# (no-op elsewhere). We avoid duplicate mounts when paths overlap
# (e.g. $PWD inside $HOME) — podman would error on that.
declare -a vols=()
vols+=("-v" "$PWD:$PWD:Z")
case "$HOME" in
    "$PWD"|"$PWD"/*) ;;  # $HOME is $PWD or contains it; skip
    *) case "$PWD" in
           "$HOME"/*) vols+=("-v" "$HOME:$HOME:Z") ;;  # cwd inside home; mount home
           *) vols+=("-v" "$HOME:$HOME:Z") ;;
       esac ;;
esac
case "/tmp" in
    "$PWD"|"$HOME"|"$PWD"/*|"$HOME"/*) ;;  # /tmp inside cwd or home; skip
    *) vols+=("-v" "/tmp:/tmp:Z") ;;
esac

exec podman run --rm -i \
    --userns=keep-id \
    "${vols[@]}" \
    --workdir="$PWD" \
    "$IMAGE_TAG" \
    "$TOOL" "$@"
