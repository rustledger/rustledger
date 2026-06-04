# LSP Support: Testing Strategy and Supported Clients

This document defines what "supported" means for `rledger-lsp`, how its
test layers map to real-world bugs, and the manual verification steps
expected before merging changes that affect editor UX.

The architectural background was driven by issues #1245 and #1253 (both
balance-lens regressions caused by client/server protocol-interaction
bugs that handler-level tests structurally could not catch). The
layered testing approach below closes that gap.

## Lens verdict source

The balance code lens does not compute its own verdict. It reads
`MainLoopState::diagnostics[uri]` — the validator's last-computed
diagnostic vector for the file — and renders one of:

- `✓ Balance: X USD` when the validator ran AND no ERROR diagnostic
  anchors on the balance directive's line.
- `⚠ Balance: X USD (see diagnostic)` when an ERROR diagnostic with a
  balance-arithmetic error code (`E2001` BalanceAssertionFailed,
  `E2002` BalanceToleranceExceeded, `E2004` MultiplePadForBalance)
  anchors on the line. "see diagnostic" is a true link by construction:
  the diagnostic the lens points at is the diagnostic the lens
  consulted. See `BALANCE_ERROR_CODES` in `handlers/code_lens.rs` for
  the full list and the rationale for excluded codes (E1001, parse
  errors, plugin errors at the line — those describe a different
  failure and surface independently).
- `Balance: X USD` (neutral, no symbol) in any of three user-facing
  conditions:
  - Cold start, before the first `publish_diagnostics` for the file.
  - Validation was skipped this turn (file > 500 KB or buffer has
    parse errors elsewhere — see `validation_would_run`).
  - A non-balance non-HINT diagnostic (e.g., `E1001 AccountNotOpen`
    ERROR, `FutureDate` WARNING, `DateOutOfOrder` INFORMATION) anchors
    on the balance directive's line — the diagnostic explains a
    different problem; claiming `⚠ Balance` would misattribute the
    failure and claiming `✓` would dismiss a real concern.
  In every neutral case the lens declines to claim a verdict it
  cannot back up.

  Internally, the first two conditions are folded into
  `verdict_diagnostics = None` by `handle_code_lens` before
  `balance_lens_title` sees them — the title function itself only
  distinguishes `None` (neutral) from `Some(diags)` with the three
  diag-content branches (balance code → ⚠, non-balance/non-HINT → 
  neutral, nothing → ✓). HINT-severity diagnostics are intentionally
  ignored: code-action hints routinely anchor on directives and would
  otherwise produce neutral noise on every code-action-eligible line.

The validator runs the full pipeline (synth-plugins → Early → book →
regular-plugins → Late) on every `didOpen` / `didChange` / `didSave`,
producing the same verdict `rledger check` does. The lens follows
that verdict.

Pre-#1264 the lens ran a separate `parse → sort → book` evaluator
that silently dropped plugins. The classic symptom was a `⚠ ...
(see diagnostic)` lens on a file `rledger check` accepted — the
"see diagnostic" link pointed nowhere because the validator (running
plugins) had not emitted one. That entire failure mode is structurally
unreachable now: the lens and the diagnostic come from the same
computation.

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
