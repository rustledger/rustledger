//! `LoadOptions::retain_source_text` integration tests.
//!
//! The flag trades the source text of every loaded file for memory once
//! processing is done. The contract this pins: what the caller gives up is
//! *post-load text access* only. Error locations are resolved while the
//! text is still held, so a dropped-text ledger reports the same
//! `file:line:col` as a retained one, and its `lineno` answers stay real
//! (the line-start table is kept), which is what BQL's `filename`/`lineno`
//! columns resolve from. A server that prints `code: message` sheds the
//! text (173 MB on the 1M-beancount workload, about 133 MB live once the
//! kept line-start table is netted out) without going blind.

use rustledger_loader::{LoadOptions, load};

/// A ledger whose validation raises located errors: an unopened account
/// and a failed balance assertion, both mid-file so a wrong line would
/// show.
const UNHAPPY_SOURCE: &str = r#"option "operating_currency" "USD"

2024-01-01 open Assets:Bank USD
2024-01-01 open Equity:Void USD

2024-01-02 * "opening"
  Assets:Bank  100 USD
  Equity:Void

2024-01-03 * "unopened"
  Assets:Never-Opened  10 USD
  Equity:Void

2024-02-01 balance Assets:Bank 999 USD
"#;

fn write_fixture(content: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .prefix("source-text-")
        .suffix(".beancount")
        .tempfile()
        .expect("create tempfile");
    std::io::Write::write_all(&mut f, content.as_bytes()).expect("write fixture");
    f
}

/// The same load with and without the text keeps every error's identity:
/// severity, code, message and location. What the dropped run loses is
/// only the text itself.
#[test]
fn error_locations_survive_the_drop() {
    let fixture = write_fixture(UNHAPPY_SOURCE);

    let retained = load(
        fixture.path(),
        &LoadOptions {
            retain_source_text: true,
            ..Default::default()
        },
    )
    .expect("load with text");

    let dropped = load(
        fixture.path(),
        &LoadOptions {
            retain_source_text: false,
            ..Default::default()
        },
    )
    .expect("load without text");

    assert!(
        !retained.errors.is_empty(),
        "fixture must raise located errors for this test to mean anything"
    );
    assert_eq!(retained.errors.len(), dropped.errors.len());

    for (keep, drop) in retained.errors.iter().zip(dropped.errors.iter()) {
        assert_eq!(keep.severity, drop.severity);
        assert_eq!(keep.code, drop.code);
        assert_eq!(keep.message, drop.message);
        let keep_loc = keep
            .location
            .as_ref()
            .expect("fixture errors carry locations");
        let drop_loc = drop.location.as_ref().expect("locations survive the drop");
        assert_eq!(keep_loc.file, drop_loc.file);
        assert_eq!(
            keep_loc.line, drop_loc.line,
            "line changed for {}",
            keep.code
        );
        assert_eq!(
            keep_loc.column, drop_loc.column,
            "column changed for {}",
            keep.code
        );
        assert!(keep_loc.line > 0, "test wants real lines, got 0");
    }
}

/// The drop is the whole point: the returned ledger holds no text, while
/// the positions BQL exposes (`filename`/`lineno`) still resolve from
/// the kept offsets table, answering exactly what a retained load does.
/// Only the line's own text and the columns counted from it go.
#[test]
fn dropped_ledger_holds_no_text() {
    let fixture = write_fixture(UNHAPPY_SOURCE);

    let retained = load(
        fixture.path(),
        &LoadOptions {
            retain_source_text: true,
            ..Default::default()
        },
    )
    .expect("load with text");

    let dropped = load(
        fixture.path(),
        &LoadOptions {
            retain_source_text: false,
            ..Default::default()
        },
    )
    .expect("load without text");

    for file in dropped.source_map.files() {
        assert!(
            !file.has_source(),
            "{} still holds text",
            file.path.display()
        );
        assert_eq!(file.source.len(), 0);
        assert_eq!(file.line(1), None);
        // Line 1 stands, column 0 without text to count in ...
        assert_eq!(file.line_col(0), (1, 0));
        // ... and the fixture's line count survives with the offsets table.
        assert!(file.num_lines() > 0);
    }
    assert!(
        !dropped.source_map.files().is_empty(),
        "paths survive the drop"
    );

    // Against the retained load: same line count, and a mid-file offset
    // (the start of the `2024-02-01 balance` line) answers the same line,
    // with the column going from real to 0.
    let [keep] = retained.source_map.files() else {
        panic!("retained load should hold exactly the fixture file");
    };
    let [drop] = dropped.source_map.files() else {
        panic!("dropped load should hold exactly the fixture file");
    };
    assert_eq!(keep.path, drop.path);
    assert_eq!(keep.num_lines(), drop.num_lines());

    let offset = UNHAPPY_SOURCE
        .find("2024-02-01 balance")
        .expect("fixture has the balance line");
    let (keep_line, keep_col) = keep.line_col(offset);
    let (drop_line, drop_col) = drop.line_col(offset);
    assert_eq!(keep_line, 14, "balance line is line 14 of the fixture");
    assert_eq!(keep_line, drop_line);
    assert_eq!(keep_col, 1);
    assert_eq!(drop_col, 0);
}

/// The default is the status quo: text is kept, snippets stay possible.
#[test]
fn text_is_retained_by_default() {
    let fixture = write_fixture(UNHAPPY_SOURCE);
    let ledger = load(fixture.path(), &LoadOptions::default()).expect("load");

    for file in ledger.source_map.files() {
        assert!(
            file.has_source(),
            "{} lost its text by default",
            file.path.display()
        );
        assert!(file.num_lines() > 0);
    }
}
