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
//! By default, fixtures whose `expected.bean` already exists are
//! skipped - so a casual re-run of the example after the initial
//! bootstrap is a no-op.
//!
//! Two env vars opt into rewriting existing golden files:
//!
//! - `BOOTSTRAP_OVERWRITE=1` - rewrite ALL existing
//!   `expected.bean` files. Reserved for the rare workflow where
//!   a deliberate formatter change rebaselines the entire suite.
//!   The example prints the list of files about to be rewritten
//!   so a casual `git diff` review catches collateral damage.
//!
//! - `BOOTSTRAP_FIXTURE=<name>` - rewrite ONLY the named fixture's
//!   `expected.bean`. Use this when one fixture needs to be
//!   rebaselined after a deliberate change to its `input.bean`
//!   (e.g. extending a #1252-style reproducer). Combining with
//!   `BOOTSTRAP_OVERWRITE` is unnecessary and ignored - naming a
//!   fixture is already an explicit opt-in to overwrite.
//!
//! Without either env var, this example is non-destructive.

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
    let overwrite_all = env::var("BOOTSTRAP_OVERWRITE").as_deref() == Ok("1");
    let target_fixture = env::var("BOOTSTRAP_FIXTURE").ok();

    // Per-entry errors panic. Silently dropping them via
    // `filter_map(Result::ok)` would silently shrink the bootstrap
    // run if a permission / filesystem fault hit one directory,
    // and the resulting "wrote N files" summary would mislead the
    // contributor into thinking the run was complete. Matches the
    // convention in `tests/baseline_common`.
    let mut fixtures: Vec<PathBuf> = fs::read_dir(&cases_dir)
        .unwrap_or_else(|e| panic!("read_dir({}): {e}", cases_dir.display()))
        .map(|entry| {
            entry.unwrap_or_else(|e| {
                panic!("read_dir entry under {} failed: {e}", cases_dir.display())
            })
        })
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    fixtures.sort();

    // If a named fixture was requested, validate it exists AND
    // has an input.bean before doing any I/O. A bare typo
    // (`BOOTSTRAP_FIXTURE=issue_1242`) and an empty-dir state
    // (`mkdir cases/new_repro` without `git add input.bean`) both
    // produced a 0-writes-and-exit-0 summary in earlier shapes
    // that the contributor would misread as "success".
    if let Some(name) = &target_fixture {
        let dir = fixtures
            .iter()
            .find(|p| p.file_name().is_some_and(|f| f == name.as_str()));
        let Some(dir) = dir else {
            eprintln!(
                "error: BOOTSTRAP_FIXTURE={name} does not match any directory in {}",
                cases_dir.display(),
            );
            std::process::exit(2);
        };
        if !dir.join("input.bean").is_file() {
            eprintln!(
                "error: BOOTSTRAP_FIXTURE={name} resolves to {} but that directory has no input.bean. \
                 Add the source-text fixture before bootstrapping the expected.",
                dir.display(),
            );
            std::process::exit(3);
        }
    }

    let mut wrote = 0;
    let mut skipped_existing = 0;
    let mut skipped_unselected = 0;
    let mut missing_input = 0;

    for fixture in &fixtures {
        let name = fixture.file_name().unwrap().to_string_lossy().into_owned();

        // Scope filter: when BOOTSTRAP_FIXTURE is set, ignore
        // every other directory.
        if let Some(target) = &target_fixture
            && &name != target
        {
            skipped_unselected += 1;
            continue;
        }

        let input_path = fixture.join("input.bean");
        let expected_path = fixture.join("expected.bean");

        if !input_path.exists() {
            eprintln!("[{name}] missing input.bean - skipped");
            missing_input += 1;
            continue;
        }
        // Overwrite gating: skip if expected.bean exists AND
        // neither overwrite flag is set for this fixture.
        let allowed_to_overwrite = overwrite_all || target_fixture.is_some();
        if expected_path.exists() && !allowed_to_overwrite {
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
        "\nbootstrap summary: {wrote} written, {skipped_existing} skipped (expected.bean already present), {skipped_unselected} skipped (unselected by BOOTSTRAP_FIXTURE), {missing_input} missing input.bean",
    );
    // The more-specific scope wins the summary message. If both
    // env vars are set, the BOOTSTRAP_FIXTURE filter takes
    // precedence (only the named fixture is written), so naming
    // that explicitly avoids the misleading "whole suite was
    // rewritten" summary the previous branch order produced.
    if target_fixture.is_some() {
        eprintln!(
            "(BOOTSTRAP_FIXTURE was set - only the named fixture's expected.bean was rewritten.)"
        );
    } else if overwrite_all {
        eprintln!(
            "(BOOTSTRAP_OVERWRITE=1 was set - existing expected.bean files were rewritten across the whole suite. \
             Review `git diff` carefully before committing.)"
        );
    } else if skipped_existing > 0 {
        eprintln!(
            "(set BOOTSTRAP_FIXTURE=<name> to re-baseline a single fixture, or \
             BOOTSTRAP_OVERWRITE=1 to re-baseline all of them; the suite-wide \
             rewrite is destructive - use sparingly.)"
        );
    }
}
