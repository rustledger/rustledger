//! Drift guard: BQL `BALANCES` and `report balances` must agree on netted
//! reductions.
//!
//! The two surfaces realize balances differently by construction: the query
//! executor re-aggregates already-booked postings with naive `Inventory::add`
//! (lot-key netting), while reports realize through the booking engine's
//! lot-matching `apply`. They agree today ONLY because both consume
//! post-booking directives — the loader's book phase has already matched
//! every reduction against its lot, so naive re-aggregation lands on the
//! same keys. That invariant holds by pipeline design, not by any type-level
//! guarantee: feeding the executor unbooked directives (a new embedding
//! path, a harness shortcut) would silently reactivate the #1726 class in
//! BQL while reports stayed correct.
//!
//! These tests pin the agreement on the two reduction shapes that killed
//! the reports in #1726: an explicit-cost reduction with a price
//! annotation, and a FIFO empty-`{}` reduction spanning two lots. If query
//! and report ever disagree here, someone changed the realization pipeline
//! — see the Phase-0 duplication registry (realization family) before
//! "fixing" either side alone.

mod common;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// Buy 10 at cost, sell 5 with explicit cost + price. Net: 5 AAPL {150.00}.
const EXPLICIT_REDUCTION: &str = r#"2024-01-01 open Assets:Broker
2024-01-01 open Assets:Cash
2024-01-01 open Income:PnL

2024-01-05 * "buy"
  Assets:Broker   10 AAPL {150.00 USD}
  Assets:Cash  -1500.00 USD

2024-06-10 * "sell half"
  Assets:Broker   -5 AAPL {150.00 USD} @ 180.00 USD
  Assets:Cash    900.00 USD
  Income:PnL    -150.00 USD
"#;

/// Two lots, FIFO reduction with an empty `{}` spec consuming lot 1 and half
/// of lot 2. Net: 5 AAPL {200.00}.
const FIFO_EMPTY_REDUCTION: &str = r#"2024-01-01 open Assets:Broker "FIFO"
2024-01-01 open Assets:Cash
2024-01-01 open Income:PnL

2024-01-05 * "buy lot1"
  Assets:Broker   10 AAPL {150.00 USD}
  Assets:Cash  -1500.00 USD

2024-02-05 * "buy lot2"
  Assets:Broker   10 AAPL {200.00 USD}
  Assets:Cash  -2000.00 USD

2024-06-10 * "sell 15 FIFO"
  Assets:Broker   -15 AAPL {} @ 180.00 USD
  Assets:Cash   2700.00 USD
  Income:PnL
"#;

fn write_fixture(source: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("realization-parity-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(source.as_bytes()).expect("write fixture");
    f
}

fn run(binary: &PathBuf, args: &[&str]) -> String {
    let out = Command::new(binary)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("run rledger {args:?}: {e}"));
    assert!(
        out.status.success(),
        "rledger {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr),
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// The Broker holding as both surfaces render it: `(units, cost-per-unit)`
/// pulled from the single line mentioning AAPL. Asserts exactly ONE such
/// line — the pre-#1726 failure shape was separate augmentation/reduction
/// rows. (The report line also carries the lot DATE, which bean-query's
/// string form omits; comparing the two extracted numbers sidesteps that
/// deliberate formatting difference.)
fn broker_holding(stdout: &str, surface: &str) -> (String, String) {
    let lines: Vec<&str> = stdout.lines().filter(|l| l.contains("AAPL")).collect();
    assert_eq!(
        lines.len(),
        1,
        "{surface} must show exactly one netted AAPL row \
         (pre-#1726 shape was split rows): {stdout}",
    );
    let numbers: Vec<&str> = lines[0]
        .split(|c: char| !c.is_ascii_digit() && c != '.' && c != '-')
        .filter(|t| !t.is_empty() && t.parse::<f64>().is_ok())
        .collect();
    assert!(
        numbers.len() >= 2,
        "{surface} AAPL row must carry units AND lot cost: {:?}",
        lines[0],
    );
    (numbers[0].to_string(), numbers[1].to_string())
}

fn assert_parity(source: &str, expected_units: &str, expected_cost: &str) {
    let bin = require_rledger!();
    let f = write_fixture(source);
    let path = f.path().to_str().unwrap();

    let query_out = run(&bin, &["query", path, "BALANCES"]);
    let report_out = run(&bin, &["report", path, "balances", "--no-pager"]);

    let query_holding = broker_holding(&query_out, "BQL BALANCES");
    let report_holding = broker_holding(&report_out, "report balances");

    assert_eq!(
        query_holding, report_holding,
        "BQL BALANCES and report balances disagree on the netted holding — \
         the realization pipeline changed; consult the duplication registry \
         (realization family) before fixing one side alone.\n\
         query: {query_out}\nreport: {report_out}",
    );
    assert_eq!(
        query_holding,
        (expected_units.to_string(), expected_cost.to_string()),
        "netted holding must be {expected_units} AAPL {{{expected_cost}}} \
         (beancount 3.2.3 parity)",
    );
}

#[test]
fn explicit_cost_reduction_nets_identically() {
    assert_parity(EXPLICIT_REDUCTION, "5", "150.00");
}

#[test]
fn fifo_empty_spec_reduction_nets_identically() {
    assert_parity(FIFO_EMPTY_REDUCTION, "5", "200.00");
}
