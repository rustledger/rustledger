//! Integration coverage for the FFI `query.execute` and `query.batch`
//! pad-expansion boundary calls (#1288, #1300).
//!
//! FFI's `load_source` does NOT go through `rustledger_loader::process`
//! (it builds directives directly from the parser+booker), so there's
//! no `Ledger` and no `balance_view()` to call. The architectural
//! rule (balance-computing consumers explicitly request the expanded
//! view) still applies; the boundary just happens to be the
//! `handle_query` / `handle_batch` entry points instead of the
//! Ledger helper.
//!
//! Pre-fix these endpoints saw raw `Pad` directives and silently
//! ignored their effect. Post-fix they merge the synth pad
//! transactions in via `rustledger_booking::merge_with_padding` at
//! the boundary.

use rustledger_ffi_wasi::jsonrpc::process_request;

const PADDED_SOURCE: &str = r#"option "operating_currency" "USD"

2026-01-01 open Assets:Wallet USD
2026-01-01 open Equity:Void USD
2026-01-01 open Expenses:Expense USD

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

/// `process_request` returns a `ResponseBatch` struct. The other FFI
/// tests round-trip it through `serde_json::to_value`; do the same.
fn rpc(req: &str) -> serde_json::Value {
    let batch = process_request(req);
    serde_json::to_value(&batch).expect("RPC response serializes to JSON")
}

/// Pull `units.number` for the row matching `account`. Pinning the
/// JSON path is robust against a substring scan over the whole
/// payload that would false-positive on numbers like `965000`.
fn unit_number_for_account(rows: &serde_json::Value, account: &str) -> Option<String> {
    let arr = rows.as_array()?;
    for row in arr {
        let cells = row.as_array()?;
        let has_account = cells.iter().any(|c| c.as_str() == Some(account));
        if !has_account {
            continue;
        }
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

/// `query.execute` against a padded ledger applies the pad's
/// effect: Assets:Wallet ends at 965 USD = 1000 (opening) - 10
/// (Jun 1 expense) - 15 (pad: 990 → 975) - 10 (Jun 2 expense).
///
/// Pre-fix the FFI path skipped expansion → query saw the `Pad`
/// directive as a no-op → Assets:Wallet showed 980 USD.
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
         pre-fix the FFI path saw 980 (pad ignored)."
    );
}

/// `query.batch` runs N queries against one load. The single
/// `expand_pads` call is hoisted above the per-query loop so every
/// query in the batch sees the expanded view. Pre-fix, the per-query
/// `execute_query` saw raw Pads → Equity:Void showed exactly -1000
/// (the opening transfer only, no pad-source adjustment).
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

    let wallet_rows = queries[0].get("rows").expect("rows[0]");
    let wallet_units = unit_number_for_account(wallet_rows, "Assets:Wallet")
        .unwrap_or_else(|| panic!("no Assets:Wallet units: {wallet_rows}"));
    assert_eq!(
        wallet_units, "965",
        "batch query[0] must also see pad expansion",
    );

    // Equity:Void: opening transfers -1000; pad-source posting puts
    // +15 back. Net: -985. Pre-fix shape was exactly -1000.
    let void_rows = queries[1].get("rows").expect("rows[1]");
    let void_units = unit_number_for_account(void_rows, "Equity:Void")
        .unwrap_or_else(|| panic!("no Equity:Void units: {void_rows}"));
    assert_eq!(
        void_units, "-985",
        "batch query[1] must see pad-source adjustment on Equity:Void; \
         pre-fix shape was exactly -1000 (pad ignored)."
    );
}
