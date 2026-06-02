//! Integration tests for `ledger.loadFile`'s `path_security` parameter.
//!
//! The default (`true`) confines the include graph to the entry file's
//! directory tree. Setting `false` opts out — verified end-to-end via
//! the JSON-RPC dispatch.
//!
//! ## Assertion strategy
//!
//! Each test pins TWO properties to avoid the "rename of error wording
//! silently inverts test polarity" failure mode:
//!
//! 1. **Structural error presence** — the result has at least one entry
//!    in `result.errors[]` whose message references a path-related
//!    rejection (loose substring match across multiple synonyms).
//! 2. **Positive load presence** — the included file's directives
//!    actually appear in (or are absent from) `result.entries[]`.
//!    A silent-drop regression in the loader that emits no error AND
//!    no entries would fail (1) cleanly; a wording-change regression
//!    that drops the substring match would still fail (2).
//!
//! The combination gives both directions structural coverage instead
//! of trusting a single brittle substring.
//!
//! See `crates/rustledger-loader/src/lib.rs::LoadError::PathTraversal`
//! for the canonical error variant the loader emits.

use rustledger_ffi_wasi::jsonrpc::process_request;
use std::fs;
use tempfile::TempDir;

/// The shared cross-tree fixture: a sibling directory containing one
/// account-opening directive that the entry file tries to include via
/// `../`. Returns `(TempDir, main_path_string)`; keep the `TempDir`
/// alive for the duration of the test so cleanup runs at drop.
fn make_cross_tree_fixture() -> (TempDir, String) {
    let dir = TempDir::new().expect("tempdir");
    let sibling_dir = dir.path().join("shared");
    fs::create_dir(&sibling_dir).expect("create shared");
    let main_dir = dir.path().join("ledger");
    fs::create_dir(&main_dir).expect("create ledger");

    fs::write(
        sibling_dir.join("accounts.bean"),
        "2024-01-01 open Assets:Cash USD\n",
    )
    .expect("write accounts");
    let main = main_dir.join("main.bean");
    fs::write(&main, "include \"../shared/accounts.bean\"\n").expect("write main");

    let main_str = main.to_str().expect("utf-8 path").to_string();
    (dir, main_str)
}

fn json_rpc_request(path: &str, path_security: Option<bool>) -> String {
    let mut params = serde_json::json!({ "path": path });
    if let Some(ps) = path_security {
        params["path_security"] = serde_json::json!(ps);
    }
    serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "ledger.loadFile",
        "params": params,
    })
    .to_string()
}

/// Path-traversal-style error detector.
///
/// Matches phrases scoped to traversal semantics specifically.
/// Previously included the bare token "outside" — too broad: any
/// future loader/booking diagnostic mentioning "outside the operating
/// range" or "outside the cost-spec tolerance" would falsely satisfy
/// this predicate, masking real path-security regressions.
///
/// Combined with the positive-entries assertion below, a wording
/// change that drops one of these specific synonyms still triggers
/// the entries-based check, so the cross-axis defense survives a
/// single-axis regression.
fn looks_like_path_security_error(message: &str) -> bool {
    let lc = message.to_lowercase();
    lc.contains("traversal")
        || lc.contains("escapes")
        || lc.contains("outside the permitted")
        || lc.contains("outside permitted")
        || lc.contains("outside the allowed")
        || lc.contains("outside allowed")
        || lc.contains("outside the base")
        || lc.contains("permitted root")
}

/// Returns true iff `result.entries[]` contains a directive whose
/// `account` field equals `Assets:Cash` — the structural fingerprint
/// of the cross-tree include having been merged into the loaded
/// ledger.
fn loaded_includes_cross_tree_open(response: &serde_json::Value) -> bool {
    let Some(entries) = response
        .pointer("/result/entries")
        .and_then(|v| v.as_array())
    else {
        return false;
    };
    entries.iter().any(|e| {
        e.get("account").and_then(|a| a.as_str()) == Some("Assets:Cash")
            || e.pointer("/account").and_then(|a| a.as_str()) == Some("Assets:Cash")
    })
}

/// Returns the messages of all `result.errors[]` entries (empty vec if
/// no errors array is present).
fn collect_load_error_messages(response: &serde_json::Value) -> Vec<String> {
    response
        .pointer("/result/errors")
        .and_then(|v| v.as_array())
        .map(|errs| {
            errs.iter()
                .filter_map(|e| e.get("message").and_then(|m| m.as_str()))
                .map(String::from)
                .collect()
        })
        .unwrap_or_default()
}

/// Default `path_security` (true) rejects an `include "../sibling"`
/// that escapes the entry file's directory. Pinned by TWO structural
/// properties: (a) a path-security-style error is present, AND
/// (b) the cross-tree directive did NOT make it into entries[]. Both
/// failure shapes (wording-rename and silent-drop) require breaking
/// both checks to slip through.
#[test]
fn default_path_security_rejects_cross_tree_include() {
    let (_dir, main_str) = make_cross_tree_fixture();
    let req = json_rpc_request(&main_str, None);
    let batch = process_request(&req);
    let response = serde_json::to_value(&batch).unwrap();

    let messages = collect_load_error_messages(&response);
    let has_path_error = response.get("error").is_some()
        || messages.iter().any(|m| looks_like_path_security_error(m));
    assert!(
        has_path_error,
        "expected a path-security rejection error, got messages: {messages:?} \
         (full response: {response})"
    );
    assert!(
        !loaded_includes_cross_tree_open(&response),
        "default path_security must NOT merge the cross-tree Assets:Cash open into entries; \
         response: {response}"
    );
}

/// Explicit `path_security: false` allows the same cross-tree include
/// AND merges its directives into the result. Without the positive
/// `entries[]` check, a silent-drop refactor (no error, no merge)
/// would pass this test — a bug class the structural assertion now
/// catches directly.
#[test]
fn path_security_false_allows_cross_tree_include() {
    let (_dir, main_str) = make_cross_tree_fixture();
    let req = json_rpc_request(&main_str, Some(false));
    let batch = process_request(&req);
    let response = serde_json::to_value(&batch).unwrap();

    assert!(
        response.get("error").is_none(),
        "expected success, got top-level error: {response}"
    );
    // No path-security error should be among result.errors.
    let messages = collect_load_error_messages(&response);
    for m in &messages {
        assert!(
            !looks_like_path_security_error(m),
            "expected no path-traversal-style error with path_security=false, got: {m}"
        );
    }
    // POSITIVE assertion: the cross-tree directive was actually loaded.
    assert!(
        loaded_includes_cross_tree_open(&response),
        "path_security=false must merge the cross-tree Assets:Cash open into entries; \
         response: {response}"
    );
}

/// Explicit `path_security: true` matches the default behavior on
/// both axes: rejection error present, no cross-tree merge.
#[test]
fn path_security_true_rejects_cross_tree_include() {
    let (_dir, main_str) = make_cross_tree_fixture();
    let req = json_rpc_request(&main_str, Some(true));
    let batch = process_request(&req);
    let response = serde_json::to_value(&batch).unwrap();

    let messages = collect_load_error_messages(&response);
    let has_path_error = response.get("error").is_some()
        || messages.iter().any(|m| looks_like_path_security_error(m));
    assert!(
        has_path_error,
        "explicit path_security=true should reject like the default, got messages: {messages:?} \
         (full response: {response})"
    );
    assert!(
        !loaded_includes_cross_tree_open(&response),
        "explicit path_security=true must NOT merge the cross-tree Assets:Cash open into entries; \
         response: {response}"
    );
}
