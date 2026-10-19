//! `py_div` against Python's `decimal` itself (#2652).
//!
//! `fixtures/py_div/cases.txt.gz` holds `a b expected tag` rows produced by
//! `fixtures/py_div/generate.py` with Python's own `decimal` module under
//! beancount's context (prec 28, `ROUND_HALF_EVEN`). Regenerate with
//!
//! ```text
//! python3 crates/rustledger-core/tests/fixtures/py_div/generate.py
//! ```
//!
//! `expected` is Python's quotient written plain (`format(q, "f")`) for every
//! row a `Decimal` can hold; the rows it cannot (`posexp`, `underflow`,
//! `underflow-zero`, `zero`, `div0`) carry the substitute `py_div` documents,
//! computed in Python from the exact quotient.

use std::collections::BTreeMap;
use std::io::Read;
use std::str::FromStr;

use rust_decimal::Decimal;
use rustledger_core::{py_compound_per_unit, py_div};

fn fixture(name: &str) -> String {
    let path = format!(
        "{}/tests/fixtures/py_div/{name}",
        env!("CARGO_MANIFEST_DIR")
    );
    let file = std::fs::File::open(path).expect("fixture exists");
    let mut text = String::new();
    flate2::read::GzDecoder::new(file)
        .read_to_string(&mut text)
        .expect("fixture is gzip text");
    text
}

#[test]
fn py_div_matches_python_decimal_on_every_fixture_row() {
    let text = fixture("cases.txt.gz");
    let mut per_tag: BTreeMap<&str, usize> = BTreeMap::new();
    let mut failures = Vec::new();
    for line in text.lines() {
        let mut fields = line.split(' ');
        let (Some(a), Some(b), Some(want), Some(tag), None) = (
            fields.next(),
            fields.next(),
            fields.next(),
            fields.next(),
            fields.next(),
        ) else {
            panic!("malformed fixture row: {line:?}");
        };
        // `from_str_exact`: an operand that does not parse exactly would test
        // a different division than Python ran.
        let da = Decimal::from_str_exact(a).unwrap_or_else(|e| panic!("{a}: {e}"));
        let db = Decimal::from_str_exact(b).unwrap_or_else(|e| panic!("{b}: {e}"));
        assert_eq!(da.to_string(), a, "operand renders as written");
        assert_eq!(db.to_string(), b, "operand renders as written");
        let got = py_div(da, db).map_or_else(|| "None".to_string(), |q| q.to_string());
        if got != want {
            failures.push(format!("{a} / {b}: got {got}, Python {want} ({tag})"));
        }
        *per_tag.entry(tag).or_default() += 1;
    }
    let total: usize = per_tag.values().sum();
    assert!(
        failures.is_empty(),
        "{} of {total} rows differ from Python; first 20:\n{}",
        failures.len(),
        failures[..failures.len().min(20)].join("\n"),
    );
    // A fixture that silently shrank would pass vacuously.
    assert!(total >= 100_000, "only {total} rows: {per_tag:?}");
    assert!(
        per_tag.get("exact-repr").copied().unwrap_or(0) >= 100_000,
        "rows checking Python's own string: {per_tag:?}"
    );
    for tag in ["posexp", "underflow", "underflow-zero", "zero", "div0"] {
        assert!(per_tag.contains_key(tag), "no {tag} rows: {per_tag:?}");
    }
}

/// `{per # total}` over `units`, against beancount's
/// `(total + per * |units|) / |units|` evaluated by Python step by step.
#[test]
fn py_compound_per_unit_matches_python_decimal_on_every_fixture_row() {
    let text = fixture("compound.txt.gz");
    let mut rows = 0usize;
    let mut checked_python_string = 0usize;
    let mut failures = Vec::new();
    for line in text.lines() {
        let f: Vec<&str> = line.split(' ').collect();
        let [per, total, units, want, tag] = f[..] else {
            panic!("malformed fixture row: {line:?}");
        };
        let d = |s: &str| Decimal::from_str_exact(s).unwrap_or_else(|e| panic!("{s}: {e}"));
        let got = py_compound_per_unit(d(per), d(total), d(units))
            .map_or_else(|| "None".to_string(), |q| q.to_string());
        if got != want {
            failures.push(format!(
                "{{{per} # {total}}} over {units}: got {got}, Python {want} ({tag})"
            ));
        }
        rows += 1;
        checked_python_string += usize::from(tag == "exact-repr");
    }
    assert!(
        failures.is_empty(),
        "{} of {rows} rows differ from Python; first 20:\n{}",
        failures.len(),
        failures[..failures.len().min(20)].join("\n"),
    );
    assert!(
        rows >= 20_000 && checked_python_string >= 15_000,
        "{rows} rows, {checked_python_string} exact"
    );
}

/// The issue's four ledgers, as beancount 3.2.3 books them.
#[test]
fn py_div_matches_beancount_on_the_issue_ledgers() {
    for (a, b, want) in [
        ("10", "4", "2.5"),
        ("10.00", "4", "2.50"),
        ("10", "3", "3.333333333333333333333333333"),
        ("7.5", "3", "2.5"),
    ] {
        let got = py_div(Decimal::from_str(a).unwrap(), Decimal::from_str(b).unwrap());
        assert_eq!(
            got.map(|q| q.to_string()).as_deref(),
            Some(want),
            "{a} / {b}"
        );
    }
}
