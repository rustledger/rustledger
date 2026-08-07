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

// ---------------------------------------------------------------------------
// #1902 Phase 3 — the same guard across the whole booking matrix.
//
// The two fixtures above pin FIFO-via-empty-`{}` and an explicit-cost
// reduction. That left five of seven booking methods unpinned, and the gap was
// load-bearing: AVERAGE diverges today (#1985). The docstring at the top of
// this file states the invariant that fails —
//
//   "they agree ... ONLY because both consume post-booking directives — the
//    loader's book phase has already matched every reduction against its lot,
//    so naive re-aggregation lands on the same keys"
//
// — and AVERAGE is the one method where a reduction is booked at a cost that
// belongs to NO augmentation (the merged average), so it has no key to net
// against and survives as a negative row.
//
// `broker_holding` above cannot express this: it asserts exactly ONE AAPL
// line, which is right for a fully netted holding and wrong for every method
// that legitimately leaves two lots standing. So the comparison below is on
// the MULTISET of (units, cost) pairs, which works whatever the shape.
// ---------------------------------------------------------------------------

/// Two lots at different costs, then a partial reduction. Parameterized by
/// booking method so every method sees an identical ledger.
fn two_lot_fixture(method: &str) -> String {
    format!(
        r#"2024-01-01 open Assets:Broker "{method}"
2024-01-01 open Assets:Cash
2024-01-01 open Income:PnL

2024-01-05 * "buy lot1"
  Assets:Broker   10 AAPL {{150.00 USD}}
  Assets:Cash  -1500.00 USD

2024-02-05 * "buy lot2"
  Assets:Broker   10 AAPL {{200.00 USD}}
  Assets:Cash  -2000.00 USD

2024-06-10 * "sell 5"
  Assets:Broker   -5 AAPL {{}} @ 180.00 USD
  Assets:Cash    900.00 USD
  Income:PnL
"#
    )
}

/// Every `(units, cost)` pair a surface reports for AAPL, sorted.
///
/// Deliberately NOT comparing rendered text. The two surfaces disagree on
/// presentation by design — the report carries the lot DATE and puts each lot
/// on its own line, BQL packs them into one cell — and a text comparison would
/// fail on that formatting difference while saying nothing about realization.
/// The lot date is dropped for the same reason the original helper dropped it.
///
/// Returns `None` when the surface reported no AAPL at all, which is distinct
/// from "reported an empty holding" and must not silently compare equal.
fn aapl_lots(stdout: &str) -> Option<Vec<(String, String)>> {
    let mut lots: Vec<(String, String)> = Vec::new();
    for line in stdout.lines().filter(|l| l.contains("AAPL")) {
        // Each lot is `<units> AAPL { <cost> CUR[, <date>]}`, possibly several
        // per line in the BQL cell.
        for chunk in line.split("AAPL").skip(1).zip(line.split("AAPL")) {
            let (after, before) = chunk;
            let units = before
                .split_whitespace()
                .next_back()
                .unwrap_or_default()
                .to_owned();
            if units.is_empty() || units.parse::<f64>().is_err() {
                continue;
            }
            // A lot with NO `{...}` is a genuine shape — NONE booking, and the
            // unbooked reduction in #1987, both produce bare units. That is
            // recorded as `None`, which is not the same as a cost that failed
            // to parse.
            //
            // Everything else fails loudly. Copilot's catch: this used to
            // `unwrap_or_default()` into an empty string, so a change to how
            // costs render would give BOTH surfaces `""` and they would
            // compare equal — a guard whose entire job is comparing costs,
            // passing precisely when it had stopped seeing them.
            let cost = match after.split_once('{') {
                None => None,
                Some((_, rest)) => {
                    let inner = rest
                        .split_once('}')
                        .unwrap_or_else(|| panic!("lot cost is not closed in {line:?}"));
                    let number = inner
                        .0
                        .split(',')
                        .next()
                        .expect("split always yields one field")
                        .split_whitespace()
                        .next()
                        .unwrap_or_else(|| panic!("lot cost carries no number in {line:?}"));
                    assert!(
                        number.parse::<f64>().is_ok(),
                        "lot cost {number:?} is not a number in {line:?} — the \
                         cost rendering changed and this comparison has stopped \
                         seeing costs"
                    );
                    Some(number.to_owned())
                }
            };
            lots.push((units, cost.unwrap_or_else(|| "<no cost>".to_owned())));
        }
    }
    if lots.is_empty() {
        return None;
    }
    lots.sort();
    Some(lots)
}

fn surfaces(method: &str) -> (Vec<(String, String)>, Vec<(String, String)>) {
    let bin = common::rledger_binary().expect("binary present");
    let f = write_fixture(&two_lot_fixture(method));
    let path = f.path().to_str().unwrap();
    let q = run(&bin, &["query", path, "BALANCES"]);
    let r = run(&bin, &["report", path, "balances", "--no-pager"]);
    (
        aapl_lots(&q).unwrap_or_else(|| panic!("BQL reported no AAPL for {method}:\n{q}")),
        aapl_lots(&r).unwrap_or_else(|| panic!("report reported no AAPL for {method}:\n{r}")),
    )
}

/// FIFO, LIFO, HIFO and NONE must realize identically on both surfaces.
///
/// Four methods, one test, because the failure mode is per-method and naming
/// them all in one assertion means a regression in exactly one still reports
/// which one.
#[test]
fn every_agreeing_booking_method_realizes_identically() {
    let _ = require_rledger!();
    let mut disagreed: Vec<String> = Vec::new();

    for method in ["FIFO", "LIFO", "HIFO", "NONE"] {
        let (query, report) = surfaces(method);
        if query != report {
            disagreed.push(format!("{method}: query={query:?} report={report:?}"));
        }
    }

    assert!(
        disagreed.is_empty(),
        "query and report disagree on realization — the pipeline changed; \
         consult the duplication registry (realization family) before fixing \
         one side alone:\n{}",
        disagreed.join("\n"),
    );
}

/// STRICT ambiguity: both surfaces report it, and they diverge on what
/// happens next — #1987.
///
/// This test used to assert only that both mentioned the message, which
/// Copilot flagged as not matching its own stated intent ("must FAIL on both
/// surfaces"). Checking the exit codes turned up a bug the message-only
/// assertion was hiding: `report balances` PANICS (exit 101, an assertion in
/// `apply()` about unbooked reductions), while `query BALANCES` exits 0 and
/// prints a `-5 AAPL` row for an account holding 15 units.
///
/// Pinned rather than skipped, for the same reason as AVERAGE below: a fix
/// changes these exit codes and trips this test, forcing it to be rewritten as
/// the agreement assertion it was always supposed to be.
#[test]
fn strict_ambiguity_is_reported_by_both_surfaces() {
    let bin = require_rledger!();
    let f = write_fixture(&two_lot_fixture("STRICT"));
    let path = f.path().to_str().unwrap();

    let query = Command::new(&bin)
        .args(["query", path, "BALANCES"])
        .output()
        .expect("run query");
    let report = Command::new(&bin)
        .args(["report", path, "balances", "--no-pager"])
        .output()
        .expect("run report");

    let combined = |o: &std::process::Output| {
        format!(
            "{}{}",
            String::from_utf8_lossy(&o.stdout),
            String::from_utf8_lossy(&o.stderr)
        )
    };
    let (q, r) = (combined(&query), combined(&report));
    assert!(
        q.contains("Ambiguous lot match"),
        "BQL must report the ambiguity: {q}"
    );
    assert!(
        r.contains("Ambiguous lot match"),
        "report must report the ambiguity: {r}"
    );

    // The outcomes, which is where they part company (#1987).
    assert!(
        query.status.success(),
        "BQL exits 0 today despite the ambiguity — if this now fails, #1987 \
         has been fixed on the query side; rewrite this test to assert both \
         surfaces agree"
    );
    assert!(
        !report.status.success(),
        "report exits non-zero today (it panics in apply()) — if this now \
         succeeds, #1987 has been fixed on the report side; rewrite this test \
         to assert both surfaces agree"
    );
    assert!(
        r.contains("panicked"),
        "the #1987 shape is a PANIC, not a clean error. If report now fails \
         cleanly that is the fix landing — rewrite this test.\nreport: {r}"
    );
}

/// AVERAGE diverges today — #1985. Pinned, not skipped.
///
/// A characterization test: it asserts the WRONG current behavior on purpose,
/// so that whichever way #1985 is fixed, this fails and forces the guard above
/// to be updated to include AVERAGE. Marking it `#[ignore]` instead would mean
/// the fix lands with nothing noticing, which is how a known divergence
/// quietly becomes a permanent one.
///
/// The report is correct (one netted `15 AAPL {175.00}`); BQL re-aggregates by
/// lot key and produces the two original lots plus a dangling `-5` at the
/// merged average cost, which belongs to no augmentation.
#[test]
fn average_booking_diverges_today() {
    let _ = require_rledger!();
    let (query, report) = surfaces("AVERAGE");

    assert_eq!(
        report,
        vec![("15".to_owned(), "175.00".to_owned())],
        "report should net AVERAGE to a single merged lot"
    );
    assert_ne!(
        query, report,
        "AVERAGE now AGREES between query and report — #1985 is fixed. \
         Delete this test and add \"AVERAGE\" to \
         `every_agreeing_booking_method_realizes_identically`."
    );
    assert!(
        query.iter().any(|(units, _)| units.starts_with('-')),
        "the #1985 shape is a surviving NEGATIVE lot; got {query:?}"
    );
}
