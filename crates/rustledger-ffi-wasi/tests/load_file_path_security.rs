//! Integration tests for `ledger.loadFile`'s `path_security` parameter.
//!
//! The default (`true`) confines the include graph to the entry file's
//! directory tree. Setting `false` opts out — verified end-to-end via
//! the JSON-RPC dispatch.

use rustledger_ffi_wasi::jsonrpc::process_request;
use std::fs;
use tempfile::TempDir;

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

/// Default `path_security` (true) rejects an `include "../sibling"` that
/// escapes the entry file's directory.
#[test]
fn default_path_security_rejects_cross_tree_include() {
    let dir = TempDir::new().unwrap();
    let sibling_dir = dir.path().join("shared");
    fs::create_dir(&sibling_dir).unwrap();
    let main_dir = dir.path().join("ledger");
    fs::create_dir(&main_dir).unwrap();

    fs::write(
        sibling_dir.join("accounts.bean"),
        "2024-01-01 open Assets:Cash\n",
    )
    .unwrap();
    let main = main_dir.join("main.bean");
    fs::write(&main, "include \"../shared/accounts.bean\"\n").unwrap();

    let req = json_rpc_request(main.to_str().unwrap(), None);
    let batch = process_request(&req);
    let bodies = serde_json::to_value(&batch).unwrap();
    // Expect an error (path-traversal rejection surfaces as a file error
    // or a load result containing PathTraversal in the errors array).
    let response = &bodies;
    let has_error = response.get("error").is_some()
        || response
            .pointer("/result/errors")
            .and_then(|v| v.as_array())
            .is_some_and(|errs| {
                errs.iter().any(|e| {
                    e.as_object()
                        .and_then(|o| o.get("message"))
                        .and_then(|m| m.as_str())
                        .is_some_and(|s| s.contains("path traversal") || s.contains("escapes"))
                })
            });
    assert!(
        has_error,
        "expected path-traversal rejection, got {response}"
    );
}

/// Explicit `path_security: false` allows the same cross-tree include.
/// Without this opt-out the previous PR was a silent BC break.
#[test]
fn path_security_false_allows_cross_tree_include() {
    let dir = TempDir::new().unwrap();
    let sibling_dir = dir.path().join("shared");
    fs::create_dir(&sibling_dir).unwrap();
    let main_dir = dir.path().join("ledger");
    fs::create_dir(&main_dir).unwrap();

    fs::write(
        sibling_dir.join("accounts.bean"),
        "2024-01-01 open Assets:Cash\n",
    )
    .unwrap();
    let main = main_dir.join("main.bean");
    fs::write(&main, "include \"../shared/accounts.bean\"\n").unwrap();

    let req = json_rpc_request(main.to_str().unwrap(), Some(false));
    let batch = process_request(&req);
    let bodies = serde_json::to_value(&batch).unwrap();
    let response = &bodies;
    // No top-level error and no path-traversal entry in result.errors.
    assert!(
        response.get("error").is_none(),
        "expected success, got top-level error: {response}"
    );
    if let Some(errs) = response
        .pointer("/result/errors")
        .and_then(|v| v.as_array())
    {
        for e in errs {
            let msg = e
                .as_object()
                .and_then(|o| o.get("message"))
                .and_then(|m| m.as_str())
                .unwrap_or("");
            assert!(
                !msg.contains("path traversal") && !msg.contains("escapes"),
                "expected no path-traversal error with path_security=false, got: {msg}"
            );
        }
    }
}

/// Explicit `path_security: true` matches the default behavior.
#[test]
fn path_security_true_rejects_cross_tree_include() {
    let dir = TempDir::new().unwrap();
    let sibling_dir = dir.path().join("shared");
    fs::create_dir(&sibling_dir).unwrap();
    let main_dir = dir.path().join("ledger");
    fs::create_dir(&main_dir).unwrap();
    fs::write(
        sibling_dir.join("accounts.bean"),
        "2024-01-01 open Assets:Cash\n",
    )
    .unwrap();
    let main = main_dir.join("main.bean");
    fs::write(&main, "include \"../shared/accounts.bean\"\n").unwrap();

    let req = json_rpc_request(main.to_str().unwrap(), Some(true));
    let batch = process_request(&req);
    let response = serde_json::to_value(&batch).unwrap();
    let has_error = response.get("error").is_some()
        || response
            .pointer("/result/errors")
            .and_then(|v| v.as_array())
            .is_some_and(|errs| {
                errs.iter().any(|e| {
                    e.as_object()
                        .and_then(|o| o.get("message"))
                        .and_then(|m| m.as_str())
                        .is_some_and(|s| s.contains("path traversal") || s.contains("escapes"))
                })
            });
    assert!(
        has_error,
        "explicit path_security=true should reject like the default: {response}"
    );
}
