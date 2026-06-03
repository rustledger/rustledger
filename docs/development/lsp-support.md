# LSP Support: Testing Strategy and Supported Clients

This document defines what "supported" means for `rledger-lsp`, how its
test layers map to real-world bugs, and the manual verification steps
expected before merging changes that affect editor UX.

The architectural background was driven by issues #1245 and #1253 (both
balance-lens regressions caused by client/server protocol-interaction
bugs that handler-level tests structurally could not catch). The
layered testing approach below closes that gap.

## Known limitations

Two cases where the lens verdict can differ from the validator:

1. **Single-file mode skips synthesizer plugins.** Files outside the
   journal (scratch buffers, files not yet `include`d) parse without
   running `auto_accounts` / `document_discovery` / user plugins.
   Ledgers that rely on plugin-synthesized directives see lens
   verdicts that disagree with `rledger check`.

2. **Multi-file mode uses the on-disk snapshot.** When the journal
   is loaded, the lens reads the post-pipeline directives from
   `LedgerState`. `didChange` does NOT trigger a journal reload (the
   full pipeline is too expensive per keystroke), so balance lenses
   on a file with unsaved edits reflect the last-saved state, not
   the current buffer. Save the file to refresh.

In both cases the diagnostic is authoritative; the lens is a fast
local approximation. A follow-up that splices the buffer into the
multi-file snapshot (like the diagnostic overlay does) would close
limitation 2.

## Validator vs lens divergence (single-file mode)

The balance code lens computes ✓ / ⚠ by booking the current file
locally. It deliberately does NOT run synthesizer plugins
(`auto_accounts`, `document_discovery`, user plugins) on every
codeLens request: running them per keystroke would dominate lens
latency. Consequence: in **single-file mode**, the lens can disagree
with `rledger check` on ledgers that rely on plugin-synthesized
directives.

In **multi-file mode** the lens uses the snapshot the LSP loaded via
`LedgerState::load`, which DID run the full pipeline. Multi-file lens
verdicts match the validator exactly (modulo bugs in either path).

When the lens diverges from the diagnostic, the diagnostic is the
source of truth. The lens is a fast local approximation.

## Supported clients

A client is "tier-1 supported" if there is at least one automated test
that drives the protocol interaction the way that client drives it, AND
a manual smoke-test checklist exists for releases that change LSP
surface area.

| Client | Tier | Quirks reproduced in tests |
|--------|------|----------------------------|
| Neovim built-in LSP (0.10+) | 1 | `nvim_cancel_race` (#1245, #1253) |
| VS Code (extension `packages/vscode`) | 1 | none required so far |
| Helix | 2 | best-effort; not in CI |
| Emacs `lsp-mode` / `eglot` | 2 | best-effort; not in CI |

Tier-1 clients block release on smoke-test failures. Tier-2 clients are
tracked but not blocking.

### Adding a new tier-1 client

1. Pick a representative real-world bug or rough edge from that client.
2. Add a quirk function in `crates/rustledger-lsp/tests/lsp_protocol/quirks.rs`
   that reproduces the buggy / surprising client pattern.
3. Add at least one integration test against the harness that exercises
   the quirk.
4. Add the manual smoke steps to the "Release smoke tests" section
   below.

## Testing layers

The LSP has three testing layers. Each layer catches a different class
of bug; relying on only one leaves the others uncovered.

### Layer 1: Handler unit tests

Location: `crates/rustledger-lsp/src/handlers/*.rs` (in `#[cfg(test)]`
modules).

Test handler functions as plain functions. Fast (microseconds), cheap
to write, run on every `cargo test`.

What they catch: incorrect output for a given input. Wrong title text,
wrong range, missing lens, etc.

What they DO NOT catch: anything about message sequencing, ordering,
cancellation, or how the client and server interleave. The handler is
correct in isolation; the bug is in the protocol dance.

### Layer 2: Protocol integration tests

Location: `crates/rustledger-lsp/tests/lsp_protocol.rs` and the
`tests/lsp_protocol/` directory.

Spawn a fresh `rledger-lsp` on a worker thread driven by an in-process
`lsp_server::Connection::memory()` channel pair. Tests drive the server
through real LSP JSON-RPC messages and assert on full message flows.

What they catch: sequencing bugs, cancellation races, state-ordering
issues, anything that needs the actual `select!` loop and the actual
notification/request/response interplay.

What they DO NOT catch: anything specific to a real client's
rendering, key bindings, autocomplete UX, or extension code.

This is the layer that catches #1245 / #1253 -class bugs.

#### How to write a Layer 2 test

```rust
use harness::{LspTestClient, test_uri};

#[test]
fn my_protocol_test() {
    let mut client = LspTestClient::spawn();
    client.initialize();

    let uri = test_uri("fixture.beancount");
    client.open_document(&uri, "2024-01-01 open Assets:Bank USD\n");

    let lenses: Option<Vec<lsp_types::CodeLens>> =
        client.request::<CodeLensRequest>(/* params */);
    // assert on the response
}
```

For race / cancellation tests, use `raw_send_request` to put the
request on the wire without blocking on the response, then send the
quirk (e.g., `quirks::nvim_cancel_race`), then read the response with
`expect_response_timeout`.

### Layer 3: Manual client smoke

Run before merging anything that changes lens text, diagnostic
publishing, completion behavior, or other client-visible surface.

The smoke takes <5 minutes and is mechanical. The point is that the
golden path renders correctly in real editors; the automated layers
cover correctness of message flow, not pixel-level rendering.

See "Release smoke tests" below.

## Release smoke tests

For every release that changes any file under `crates/rustledger-lsp/`
or `packages/vscode/`:

### Neovim (0.10+)

1. `cargo install --path crates/rustledger-lsp --bin rledger-lsp`
2. Open a sample `.beancount` file with a balance assertion and at
   least one open / close directive.
3. Verify the balance code lens renders with `✓` or `⚠` text on first
   draw. It must not show `(checking…)` or any other placeholder.
4. Edit the file to invalidate the balance, save, and verify the lens
   flips to `⚠` within a few hundred ms.
5. Trigger completion in an account context. Verify it lists open
   accounts.

### VS Code

1. Build the extension: `cd packages/vscode && npm ci && npm run package`.
2. Install the `.vsix` and reload the window.
3. Open a sample `.beancount` file and repeat steps 3-5 above.

Document any new failures as a tier-1 quirk per the "Adding a new
tier-1 client" section.
