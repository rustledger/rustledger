//! Read every `cases/*/input.bean` and write `cases/*/expected.bean`
//! by running it through `format_source`. Used once when authoring
//! the format-compat suite (#1262 phase 4.2); after that the
//! expected.bean files are checked-in golden bytes and any drift
//! between the formatter and an expected file fails the
//! `format_compat` integration test.
//!
//! Run with:
//!   `cargo run --example bootstrap_format_compat -p rustledger-parser`
//!
//! Refuses to overwrite an existing expected.bean unless
//! `BOOTSTRAP_OVERWRITE=1` is set, so a stray re-run doesn't quietly
//! re-baseline a fixture whose expected.bean was hand-edited to pin a
//! deliberate canonical-form choice.

use rustledger_parser::format::format_source;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

fn main() {
    let cases_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("format_compat")
        .join("cases");
    if !cases_dir.is_dir() {
        eprintln!("error: cases dir not found: {}", cases_dir.display());
        std::process::exit(1);
    }
    let overwrite = env::var("BOOTSTRAP_OVERWRITE").as_deref() == Ok("1");

    let mut fixtures: Vec<PathBuf> = fs::read_dir(&cases_dir)
        .expect("read_dir cases")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    fixtures.sort();

    let mut wrote = 0;
    let mut skipped_existing = 0;
    let mut missing_input = 0;

    for fixture in &fixtures {
        let name = fixture.file_name().unwrap().to_string_lossy().into_owned();
        let input_path = fixture.join("input.bean");
        let expected_path = fixture.join("expected.bean");

        if !input_path.exists() {
            eprintln!("[{name}] missing input.bean — skipped");
            missing_input += 1;
            continue;
        }
        if expected_path.exists() && !overwrite {
            skipped_existing += 1;
            continue;
        }

        let input = fs::read_to_string(&input_path)
            .unwrap_or_else(|e| panic!("[{name}] read input.bean: {e}"));
        let formatted = format_source(&input);
        fs::write(&expected_path, &formatted)
            .unwrap_or_else(|e| panic!("[{name}] write expected.bean: {e}"));
        eprintln!("[{name}] wrote expected.bean ({} bytes)", formatted.len());
        wrote += 1;
    }

    eprintln!(
        "\nbootstrap summary: {wrote} written, {skipped_existing} skipped (expected.bean already present), {missing_input} missing input.bean",
    );
    if overwrite {
        eprintln!("(BOOTSTRAP_OVERWRITE=1 was set — existing expected.bean files were rewritten)");
    } else if skipped_existing > 0 {
        eprintln!(
            "(set BOOTSTRAP_OVERWRITE=1 to re-baseline existing expected.bean files; \
             use sparingly — they're the golden contract)"
        );
    }
}
