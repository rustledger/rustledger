//! Round-2 verification coverage for the FFI `query.execute` and
//! `query.batch` pad-expansion fixes (PR #1301).
//!
//! Round-0 already verified end-to-end via the CLI integration tests
//! that the loader-side pad expansion makes `rledger query` show the
//! correct numbers. The FFI path is separate — `load_source` in
//! `helpers.rs:86` builds directives directly from
//! `parse_result.directives` and never calls `rustledger_loader::process`,
//! so the loader-side expansion that #1288 added does NOT reach the
//! JSON-RPC layer. Round-1 added explicit `expand_pads(&load.directives)`
//! calls at the FFI boundary in `handle_query` and (round-2) in the
//! batch executor in `handle_batch`. These tests pin that behavior so
//! a future refactor (e.g. routing FFI through `process()`) can't
//! silently regress to the empty-padding-transactions shape.

use rustledger_ffi_wasi::jsonrpc::process_request;

const PADDED_SOURCE: &str = r#"option "operating_currency" "USD"

2026-01-01 open Assets:Wallet USD
2026-01-01 open Equity:Void USD

2026-01-01 * "opening"
  Assets:Wallet  1000 USD
  Equity:Void

2026-06-01 * "expense"
  Expenses:Expense  10 USD
  Assets:Wallet

2026-06-01 pad Assets:Wallet Equity:Void
2026-06-02 balance Assets:Wallet 975 USD

2026-06-02 * "expense"
  Expenses:Expense  10 USD
  Assets:Wallet
"#;

/// Pull out the first position's `units.number` from the row
/// matching `account`. The query result shape is
/// `[[<account_str>, {"positions": [{"units": {"number": "965",
/// "currency": "USD"}}]}], ...]`. A flat string scan over the whole
/// payload would risk false-positives on substrings like `965000` —
/// pinning the row + the JSON path is robust against report layout
/// changes that don't reshape this column.
fn unit_number_for_account(rows: &serde_json::Value, account: &str) -> Option<String> {
    let arr = rows.as_array()?;
    for row in arr {
        let cells = row.as_array()?;
        let has_account = cells.iter().any(|c| c.as_str() == Some(account));
        if !has_account {
            continue;
        }
        // Find the inventory/position cell and dive in.
        for cell in cells {
            if let Some(positions) = cell.get("positions").and_then(|p| p.as_array())
                && let Some(first) = positions.first()
                && let Some(n) = first
                    .get("units")
                    .and_then(|u| u.get("number"))
                    .and_then(|n| n.as_str())
            {
                return Some(n.to_string());
            }
        }
    }
    None
}

/// `process_request` returns a `ResponseBatch` struct (single or
/// array). The other FFI tests round-trip it through `serde_json::to_value`
/// to get a `serde_json::Value` for indexing; do the same here.
fn rpc(req: &str) -> serde_json::Value {
    let batch = process_request(req);
    serde_json::to_value(&batch).expect("RPC response serializes to JSON")
}

/// `query.execute` against a padded ledger must apply the pad's
/// effect (Assets:Wallet ends at 965 USD = 1000 - 10 - 15 - 10).
///
/// Pre-PR-#1301: FFI's `load_source` skipped `expand_pads` → query
/// saw `Pad` directive as a no-op → Assets:Wallet showed 980 USD.
/// Round-1: explicit `rustledger_booking::expand_pads` call at the
/// FFI boundary recovered correct behavior.
#[test]
fn query_execute_applies_pad_expansion() {
    let req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "query.execute",
        "params": {
            "source": PADDED_SOURCE,
            "query": "SELECT account, sum(position) WHERE account = 'Assets:Wallet'",
        },
    })
    .to_string();

    let parsed = rpc(&req);

    assert!(
        parsed.get("error").is_none(),
        "RPC error: {}",
        parsed.get("error").unwrap_or(&serde_json::Value::Null)
    );
    let result = parsed.get("result").expect("result field");
    let rows = result.get("rows").expect("rows field");

    let units = unit_number_for_account(rows, "Assets:Wallet")
        .unwrap_or_else(|| panic!("no Assets:Wallet units in rows: {rows}"));
    assert_eq!(
        units, "965",
        "Assets:Wallet must be 965 USD (pad expanded); \
         pre-fix the FFI path saw 980 (pad ignored).",
    );
}

/// `query.batch` runs N queries against one load. Round-1 left the
/// batch path unfixed — each query still saw the unexpanded directive
/// list. Round-2 hoisted a single `expand_pads` call above the
/// per-query loop. Verify both queries see the pad effect.
#[test]
fn query_batch_applies_pad_expansion_to_every_query() {
    let req = serde_json::json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "query.batch",
        "params": {
            "source": PADDED_SOURCE,
            "queries": [
                "SELECT account, sum(position) WHERE account = 'Assets:Wallet'",
                "SELECT account, sum(position) WHERE account = 'Equity:Void'",
            ],
        },
    })
    .to_string();

    let parsed = rpc(&req);

    assert!(
        parsed.get("error").is_none(),
        "RPC error: {}",
        parsed.get("error").unwrap_or(&serde_json::Value::Null),
    );

    let result = parsed.get("result").expect("result field");
    let queries = result
        .get("queries")
        .and_then(|q| q.as_array())
        .expect("queries array");
    assert_eq!(queries.len(), 2, "two queries → two results");

    // First query: Assets:Wallet = 965 USD (post-pad).
    let wallet_rows = queries[0].get("rows").expect("rows[0]");
    let wallet_units = unit_number_for_account(wallet_rows, "Assets:Wallet")
        .unwrap_or_else(|| panic!("no Assets:Wallet units: {wallet_rows}"));
    assert_eq!(
        wallet_units, "965",
        "batch query[0] must also see pad expansion",
    );

    // Second query: Equity:Void reflects the synth posting from the
    // pad. Opening transfers 1000 USD into Assets:Wallet (so Void is
    // -1000). The pad-source posting at Jun 1 puts +15 back into
    // Equity:Void (the synth's source posting holds the negation of
    // the target adjustment). Net: -985.
    //
    // Pre-round-2-fix: per-query `expand_pads` ran but the input
    // directive list passed to `execute_query` still contained the
    // raw `Pad` directive, which the query engine ignores → Void
    // would show exactly -1000 (the opening transfer only). Asserting
    // the post-fix value pins the behavior we want and would fail
    // cleanly on the pre-fix shape.
    let void_rows = queries[1].get("rows").expect("rows[1]");
    let void_units = unit_number_for_account(void_rows, "Equity:Void")
        .unwrap_or_else(|| panic!("no Equity:Void units: {void_rows}"));
    assert_eq!(
        void_units, "-985",
        "batch query[1] must see pad-source adjustment on Equity:Void; \
         pre-round-2-fix shape was exactly -1000 (pad ignored)",
    );
}
