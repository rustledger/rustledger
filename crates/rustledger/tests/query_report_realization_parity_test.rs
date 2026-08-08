//! Drift guard: BQL `BALANCES` and `report balances` must agree on netted
//! reductions.
//!
//! The two surfaces now realize balances the SAME way — both through
//! `BookingEngine`, which resolves the account's booking method and reduces
//! against a lot or adds a new one.
//!
//! They did not always. Until #1985 the query executor re-aggregated
//! already-booked postings with a naive `Inventory::add` — unconditionally,
//! with no reduction branch at all — and this file used to explain that the
//! two agreed "ONLY because both consume post-booking directives ... so naive
//! re-aggregation lands on the same keys". That was true for FIFO/LIFO/HIFO
//! and false for AVERAGE, where a reduction is booked at the merged average
//! cost, a key belonging to no augmentation. It survived as a dangling
//! negative position, and BQL reported a negative holding for an account that
//! held 15 units.
//!
//! Recorded rather than deleted because the shape recurs: an invariant that
//! holds "by pipeline design, not by any type-level guarantee" is one nobody
//! is checking, and the exception had been shipping for as long as AVERAGE
//! had. These tests are that check.
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
// load-bearing: extending the matrix is what found #1985 (AVERAGE realizing
// differently on the two surfaces) and #1987 (STRICT ambiguity panicking one
// surface while the other answered wrongly). Both are fixed; the matrix stays
// so the next method added is pinned from the start rather than five releases
// later.
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
{reduction}
  Assets:Cash    900.00 USD
  Income:PnL
"#,
        reduction = reduction_for(method),
    )
}

/// The reduction line, which cannot be the same for every method.
///
/// NONE turns cost tracking off, so an empty `{{}}` spec has nothing to
/// resolve and interpolation fails with "2 unknowns" — the transaction never
/// books at all. Before #1987 that did not show up here, because both surfaces
/// then realized the UNBOOKED transaction and agreed: the guard was comparing
/// two wrong answers and calling it parity. Making booking failures fatal is
/// what exposed it.
///
/// NONE therefore reduces by price rather than by lot, which is the only shape
/// that means anything when there are no lots.
fn reduction_for(method: &str) -> &'static str {
    if method == "NONE" {
        "  Assets:Broker   -5 AAPL @ 180.00 USD"
    } else {
        "  Assets:Broker   -5 AAPL {} @ 180.00 USD"
    }
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

/// Every booking method must realize identically on both surfaces.
///
/// FIFO, LIFO, HIFO, NONE and — since #1985 — AVERAGE. One test rather than
/// five, because the failure mode is per-method and collecting the
/// disagreements means a regression in exactly one still names which one.
///
/// AVERAGE is asserted again on its own below, for the netted SHAPE that set
/// comparison cannot express.
#[test]
fn every_agreeing_booking_method_realizes_identically() {
    let _ = require_rledger!();
    let mut disagreed: Vec<String> = Vec::new();

    for method in ["FIFO", "LIFO", "HIFO", "NONE", "AVERAGE"] {
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

/// STRICT ambiguity: both surfaces must REFUSE, alike.
///
/// This test was a characterization test for #1987 and has been rewritten
/// because the fix tripped it, which is exactly what it was for. What it used
/// to pin:
///
/// | surface | exit | behavior |
/// |---|---|---|
/// | `query BALANCES` | 0 | printed `-5 AAPL` for an account holding 15 |
/// | `report balances` | 101 | **panicked** in `apply()` |
///
/// One crashed, the other answered wrongly, and neither said so in its exit
/// code. Now both refuse with the same message and the same status: a
/// transaction that did not book leaves the stream in pre-booking shape, and
/// no figure derived from it can be trusted.
///
/// Asserting the STATUS and not only the message, which is the gap that hid
/// the panic: the old version checked that both *printed* the ambiguity, and
/// both did — one of them on its way to crashing.
#[test]
fn strict_ambiguity_makes_both_surfaces_refuse() {
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
        !query.status.success(),
        "BQL must refuse to answer over an unbooked ledger: {q}"
    );
    assert!(
        !report.status.success(),
        "report must refuse to answer over an unbooked ledger: {r}"
    );
    for (surface, out) in [("query", &q), ("report", &r)] {
        assert!(
            out.contains("could not be booked"),
            "{surface} must say WHY it refused: {out}"
        );
        assert!(
            out.contains("Ambiguous lot match"),
            "{surface} must name the underlying booking failure: {out}"
        );
        assert!(
            !out.contains("panicked"),
            "{surface} must fail cleanly, not panic (#1987): {out}"
        );
    }
}

/// `--no-errors` suppresses PRINTING, not the refusal.
///
/// Copilot's catch on the #1987 fix: the guard was nested inside the
/// `!args.no_errors` block, so `rledger query --no-errors x BALANCES` walked
/// straight past a booking failure and printed the dangling `-5 AAPL` row with
/// exit 0 — the exact bug the fix exists to prevent, reachable through a flag
/// about verbosity.
///
/// Note the argument ORDER. `rledger query FILE QUERY --no-errors` puts the
/// flag after the positionals, where it is swallowed into the BQL text and
/// never registers — which is how the first attempt to reproduce this
/// "passed". The flag has to come before the positionals to mean anything.
#[test]
fn no_errors_does_not_permit_answering_from_an_unbooked_ledger() {
    let bin = require_rledger!();
    let f = write_fixture(&two_lot_fixture("STRICT"));
    let path = f.path().to_str().unwrap();

    let out = Command::new(&bin)
        .args(["query", "--no-errors", path, "BALANCES"])
        .output()
        .expect("run query");
    let stdout = String::from_utf8_lossy(&out.stdout);

    assert!(
        !out.status.success(),
        "--no-errors must not license answering over an unbooked ledger: {stdout}"
    );
    assert!(
        !stdout.contains("AAPL"),
        "no holding may be reported from an unbooked ledger: {stdout}"
    );
}

/// AVERAGE too — the divergence #1985 named, now fixed.
///
/// This replaces `average_booking_diverges_today`, a characterization test
/// that asserted the WRONG behavior on purpose so a fix would trip it. It did,
/// which is what it was for. What it used to pin:
///
/// | surface | AAPL for an account holding 15 |
/// |---|---|
/// | `report balances` | `15 AAPL {175.00}` |
/// | `query BALANCES` | `10 {200}` + `10 {150}` + **`-5 {175}`** |
///
/// The cause was two realizations of one ledger. BQL accumulated with
/// `Inventory::add` unconditionally, with no reduction branch at all — right
/// for FIFO/LIFO by coincidence, because booking has already resolved a
/// reduction's cost so its lot key matches an existing lot and `add` nets it.
/// Under AVERAGE the reduction is booked at the MERGED average cost, a key
/// belonging to no augmentation, so it survived as a dangling negative.
///
/// BQL now realizes through `BookingEngine::apply_posting`, the same decision
/// reports use, so this is one realization rather than two that agree by
/// luck.
///
/// Kept SEPARATE from the loop above rather than folded into it, because the
/// netting is what makes AVERAGE different: it is the only method whose
/// holding collapses to a single lot, and asserting that shape is worth more
/// than one more iteration of a set comparison.
///
/// DELIBERATE DEVIATION, and the reason this bug needed an internal guard.
/// Python beancount does NOT implement AVERAGE: `booking_method_AVERAGE`
/// raises `AmbiguousMatchError("AVERAGE method is not supported")` and the real
/// implementation sits commented out ("DISABLED - This is the code for
/// AVERAGE"). Run this fixture through beancount and it books no reduction at
/// all, leaving 20 units.
///
/// So there is no oracle for this. The compat suite cannot referee it, and the
/// value asserted here rests on the definition instead: 10 @ 150 plus 10 @ 200
/// is 3500 over 20 units, so 175.00 per unit; selling 5 leaves 15 at 175.00.
/// That is textbook average-cost, and it is what both surfaces now produce.
///
/// Worth stating because it is the general case, not a footnote: a divergence
/// in a feature the reference implementation does not have is invisible to
/// differential testing by construction. The parity guard between our OWN two
/// surfaces is the only thing that could have found it.
#[test]
fn average_booking_nets_to_a_single_merged_lot() {
    let _ = require_rledger!();
    let (query, report) = surfaces("AVERAGE");

    assert_eq!(
        report,
        vec![("15".to_owned(), "175.00".to_owned())],
        "report must net AVERAGE to one merged lot"
    );
    assert_eq!(
        query, report,
        "BQL must realize AVERAGE the same way the report does (#1985)"
    );
    assert!(
        !query.iter().any(|(units, _)| units.starts_with('-')),
        "a negative holding is the #1985 shape and must not return: {query:?}"
    );
}
