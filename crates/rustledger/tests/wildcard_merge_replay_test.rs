//! A carried `{*}` must not turn a FILTERED query into an error (#2068).
//!
//! Booking cannot resolve `{*}` into the lot it picked, because the merged
//! pool does not exist until the merge runs — so the marker is carried and
//! the booked posting re-executes the merge wherever it is applied.
//!
//! That makes the posting sensitive to the state it meets, and `apply` checks
//! it against the pool booking recorded. The query executor is the one caller
//! that must NOT be checked that way: a `FROM` filter deliberately replays a
//! subset of the transactions, so a different pool is the correct answer for
//! the stream it was given, not evidence of corruption. Checking inside
//! `replay_posting` (which the executor calls directly) aborted such a query
//! with a `{*}` merge mismatch.

mod common;

use std::io::Write;
use std::process::Command;

/// Two lots at 100 and 120, then a `{*}` sale booked against the 110 pool.
const MERGE_SOURCE: &str = r#"2000-01-01 open Assets:Stock X "STRICT"
2000-01-01 open Assets:Cash USD
2000-01-01 open Income:PnL

2024-01-01 * "buy lot 1"
  Assets:Stock  10 X {100.00 USD}
  Assets:Cash  -1000.00 USD

2024-01-02 * "buy lot 2"
  Assets:Stock  10 X {120.00 USD}
  Assets:Cash  -1200.00 USD

2024-02-01 * "sell against the merged pool"
  Assets:Stock  -5 X {*}
  Assets:Cash   600.00 USD
  Income:PnL
"#;

#[test]
fn a_from_filter_that_drops_a_merged_lot_still_answers() {
    let Some(binary) = common::rledger_binary() else {
        eprintln!("rledger binary not built; skipping");
        return;
    };
    let mut f = tempfile::Builder::new()
        .prefix("wildcard-merge-replay-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(MERGE_SOURCE.as_bytes()).expect("write fixture");
    let path = f.path().to_string_lossy().into_owned();

    // Excludes the 100.00 lot, so the replayed stream merges only the 120.00
    // one — a pool booking never saw, and the right answer for this stream.
    let out = Command::new(&binary)
        .args([
            "query",
            &path,
            "select account, account_balance from not (narration ~ 'lot 1') \
             where account ~ 'Stock'",
        ])
        .output()
        .expect("run rledger query");

    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "a filtered replay must re-derive the pool, not report a mismatch: {stderr}",
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("120.00") && !stdout.contains("110.00"),
        "the filtered stream holds only the 120.00 lot: {stdout}",
    );
}
