//! Regression test for L3: `doctor region --conversion cost` must cost
//! compound (`{a # b}`) lots correctly.
//!
//! `doctor region` reads the RAW load stream — before booking rewrites
//! `Compound` to `PerUnitFromTotal` — so it is the one CLI surface where
//! `Compound` reaches cost math as-written. Pre-fix, the
//! `total()`/`per_unit()` accessor chain returned `None` for `Compound`
//! and fell through to the bare unit count mislabeled with the cost
//! currency: `10 WIDGET {5.00 # 10.00 USD}` displayed as `10 USD`
//! instead of `60.00 USD` (N·a + b), and the "net changes" view did not
//! balance.

mod common;

use std::io::Write;

const COMPOUND_SOURCE: &str = r#"2024-01-01 open Assets:Broker
2024-01-01 open Assets:Cash

2024-01-05 * "buy with compound cost"
  Assets:Broker   10 WIDGET {5.00 # 10.00 USD}
  Assets:Cash   -60.00 USD
"#;

#[test]
fn doctor_region_costs_compound_lots() {
    let bin = require_rledger!();
    let mut f = tempfile::Builder::new()
        .prefix("doctor-compound-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    f.write_all(COMPOUND_SOURCE.as_bytes())
        .expect("write fixture");
    let out = std::process::Command::new(&bin)
        .args([
            "doctor",
            "region",
            f.path().to_str().unwrap(),
            "1",
            "20",
            "--conversion",
            "cost",
        ])
        .output()
        .expect("run doctor region");
    assert!(out.status.success(), "doctor region failed");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("Assets:Broker 60.00 USD"),
        "compound cost must total N*a+b = 60.00 USD on the Broker line \
         (a bare \"60.00 USD\" match would be satisfied by the cash leg \
         and pass even under the pre-fix bug; deep-review catch): {stdout}",
    );
    assert!(
        !stdout.contains("Assets:Broker 10 USD"),
        "the unit-count-mislabeled-as-cost bug must not reappear: {stdout}",
    );
}
