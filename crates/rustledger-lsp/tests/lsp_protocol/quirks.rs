//! Client-specific quirks the harness reproduces.
//!
//! Each function encodes a known buggy or surprising pattern in a
//! real LSP client we care about. Tests use these instead of writing
//! the raw message sequence inline, so the quirk's documentation
//! lives in one place and a single fix (or upstream client fix)
//! updates every test at once.
//!
//! When you add a quirk, document:
//! - which client exhibits it
//! - the user-visible symptom it caused on our side
//! - the issue number(s) where we encountered it
//! - what the quirk function actually sends

use lsp_server::RequestId;

use crate::harness::LspTestClient;

/// nvim's built-in LSP client (as of 0.10+) sends `$/cancelRequest`
/// very aggressively, frequently while a request is still in
/// flight. When the cancel arrives between the time we receive the
/// request and the time we send the response, nvim has been
/// observed to discard the response if the request id is no longer
/// tracked on its side. The user-visible symptom: code lenses get
/// stuck on whatever placeholder text shipped with the initial
/// response (issues #1245 / #1253), since `codeLens/resolve`
/// responses race-and-lose with cancellation.
///
/// This helper simulates the race directly: after `client.request()`
/// has put a request on the wire, call `nvim_cancel_race(id)` to
/// fire a cancel for that id while the server may still be
/// processing it. A correctly-architected server (no resolve
/// round-trip; see #1260) ships the final lens on the initial
/// response, so this race becomes structurally impossible, which
/// is exactly the invariant the tests against this quirk pin.
pub fn nvim_cancel_race(client: &LspTestClient, id: &RequestId) {
    client.cancel(id);
}
