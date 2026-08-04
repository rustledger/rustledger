//! Cache round-trip properties (#1902, Phase 1).
//!
//! The existing cache tests hand-build a `CacheEntry` from a literal directive.
//! That proves the archive format works on the shape the test author thought
//! of, which is not the shape that keeps breaking.
//!
//! What keeps breaking is a PARSER change that alters output while the archive
//! layout stays put — the loader then accepts an old blob quite happily and
//! serves the pre-fix parse. That is not theoretical: during #1942 the parser
//! was provably fixed (a probe showed the corrected cost) while `rledger check`
//! still reported the old imbalance, because a stale cache was answering.
//!
//! So these round-trip REAL PARSED LEDGERS, one per shape that moved recently,
//! and assert the directives survive byte-for-byte. A regression in archiving
//! any of these fails here rather than in a user's stale cache.

use std::fs;
use std::io::Write;

/// One ledger per shape whose parser output changed in the 2026-08 series.
/// Each is a case where a stale cache would have served a materially wrong
/// answer, not merely a differently-formatted one.
fn shapes() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "cost_arithmetic",
            // #1939: `{10.00 * 3 USD}` booked 10.00 before the fix.
            "2013-01-01 open Assets:S\n2013-01-01 open Assets:C\n\
             2013-05-18 * \"t\"\n  Assets:S  2 HOOL {10.00 * 3 USD}\n  Assets:C -60.00 USD\n",
        ),
        (
            "negative_cost",
            // #1939 again: the sign was dropped, booking +200.00.
            "2013-01-01 open Assets:M\n2013-01-01 open Assets:C\n\
             2013-05-18 * \"t\"\n  Assets:M  -10 MSFT {-200.00 USD}\n  Assets:C 2000.00 USD\n",
        ),
        (
            "compound_cost",
            // #1943: we keep the written numbers where beancount solves.
            "2014-01-01 open Assets:A\n2014-01-01 open Assets:C\n\
             2014-01-01 * \"t\"\n  Assets:A  10 AAPL {# 9.95 USD}\n  Assets:C -9.95 USD\n",
        ),
        (
            "metadata_arithmetic",
            // #1944: `2 * 3` archived as 2 before the fix.
            "2013-01-01 open Assets:A\n2013-01-01 open Assets:B\n\
             2013-05-18 * \"t\"\n  num: 2 * 3\n  Assets:A  10.00 USD\n  Assets:B -10.00 USD\n",
        ),
        (
            "balance_tolerance_arithmetic",
            // #1944: `~ 0.005 * 2` archived as 0.005, rejecting a valid file.
            "2013-01-01 open Assets:A\n2013-01-01 open Assets:B\n\
             2013-05-18 * \"t\"\n  Assets:A  10.008 USD\n  Assets:B -10.008 USD\n\
             2014-01-01 balance Assets:A 10.00 ~ 0.005 * 2 USD\n",
        ),
        (
            "unicode_account",
            // #1930: this file did not parse at all before the fix.
            "2018-01-01 open Assets:CORP\u{2728}\n2018-01-01 open Assets:C\n\
             2018-06-01 * \"t\"\n  Assets:CORP\u{2728}  1.00 USD\n  Assets:C -1.00 USD\n",
        ),
        (
            "tags_and_links",
            "2018-01-01 open Assets:A\n2018-01-01 open Assets:B\n\
             2018-06-01 * \"t\" #tag ^link\n  Assets:A  1.00 USD\n  Assets:B -1.00 USD\n",
        ),
        (
            "lots_and_prices",
            "2018-01-01 open Assets:B\n2018-01-01 open Assets:C\n2018-01-01 open Income:G\n\
             2018-02-01 * \"buy\"\n  Assets:B  10 CORP {12.00 USD}\n  Assets:C -120.00 USD\n\
             2018-06-01 * \"sell\"\n  Assets:B -10 CORP {12.00 USD} @ 15.00 USD\n\
             \x20 Assets:C  150.00 USD\n  Income:G  -30.00 USD\n",
        ),
    ]
}

/// Fail fast if the cache env vars are set.
///
/// `save_cache_entry` / `load_cache_entry` read process env, so an inherited
/// `BEANCOUNT_LOAD_CACHE_FILENAME` would redirect these writes out of the
/// fixture — silently making the round-trip assert nothing, or clobbering a
/// developer's real cache file. The unit tests in `cache.rs` guard themselves
/// the same way (`assert_clean_cache_env`); this is that check, for a test
/// binary that cannot see it.
///
/// CLAUDE.md warns against asserting environment as a precondition (#1729).
/// The exception earns itself here: the alternative is not a hermetic test but
/// a test that writes somewhere unexpected, and failing loudly beats that.
fn assert_clean_cache_env() {
    for var in [
        rustledger_loader::CACHE_FILENAME_ENV,
        rustledger_loader::DISABLE_CACHE_ENV,
    ] {
        assert!(
            std::env::var_os(var).is_none(),
            "unset {var} before running this test - it redirects or disables \
             the cache these properties are about",
        );
    }
}

/// A fixture directory unique to this process and call.
///
/// Not a fixed name under `std::env::temp_dir()`: two concurrent `cargo test`
/// processes would land on the same path, and the cleanup at the start would
/// delete the other run's fixture out from under it. `TempDir` also removes
/// itself when dropped, so a failing assertion does not leave litter behind.
fn fixture_dir() -> tempfile::TempDir {
    tempfile::Builder::new()
        .prefix("rledger_cache_props_")
        .tempdir()
        .expect("temp dir")
}

/// Parsing, archiving and reading back must yield the SAME directives.
///
/// Asserted on the `Debug` rendering of the whole directive vector: this is a
/// round-trip identity check, so coupling to formatting is the point — any
/// field that fails to survive shows up, including ones no accessor exposes.
#[test]
fn cache_roundtrip_preserves_parsed_directives() {
    assert_clean_cache_env();
    for (name, source) in shapes() {
        let dir = fixture_dir();
        let file = dir.path().join("main.beancount");
        let mut f = fs::File::create(&file).expect("create");
        f.write_all(source.as_bytes()).expect("write");
        drop(f);

        let mut loader = rustledger_loader::Loader::new();
        let loaded = loader.load(&file).expect("load");

        // Without this the comparison below is satisfied by two empty vectors,
        // and a shape that stopped parsing would pass as a clean round-trip.
        // Every fixture here is a multi-directive ledger, so anything under 2
        // means the source stopped being what this case is about.
        assert!(
            loaded.directives.len() >= 2,
            "{name}: expected a multi-directive parse, got {} — the fixture is \
             no longer exercising this shape",
            loaded.directives.len(),
        );

        let entry = rustledger_loader::CacheEntry {
            directives: loaded.directives.clone(),
            options: rustledger_loader::CachedOptions::from(&loaded.options),
            plugins: Vec::new(),
            files: vec![file.to_string_lossy().into_owned()],
        };
        rustledger_loader::save_cache_entry(&file, &entry).expect("save");
        let back = rustledger_loader::load_cache_entry(&file).expect("load cache");

        assert_eq!(
            format!("{:?}", back.directives),
            format!("{:?}", entry.directives),
            "{name}: directives did not survive the cache round-trip",
        );
        rustledger_loader::invalidate_cache(&file);
    }
}

/// A blob written under an OLDER version must be refused, not reinterpreted.
///
/// This is the property that actually protects users across an upgrade: the
/// archive layout often does NOT change when parser output does, so nothing
/// stops an old blob from deserializing cleanly into the new types and serving
/// a pre-fix answer. Only the version check stands between that and a wrong
/// number on screen.
#[test]
fn a_stale_version_is_refused_rather_than_reinterpreted() {
    assert_clean_cache_env();
    let dir = fixture_dir();
    let file = dir.path().join("main.beancount");
    let mut f = fs::File::create(&file).expect("create");
    f.write_all(b"2018-01-01 open Assets:A\n").expect("write");
    drop(f);

    let mut loader = rustledger_loader::Loader::new();
    let loaded = loader.load(&file).expect("load");
    let entry = rustledger_loader::CacheEntry {
        directives: loaded.directives.clone(),
        options: rustledger_loader::CachedOptions::from(&loaded.options),
        plugins: Vec::new(),
        files: vec![file.to_string_lossy().into_owned()],
    };
    rustledger_loader::save_cache_entry(&file, &entry).expect("save");

    // Rewrite the version word in the header to the previous version.
    let path = rustledger_loader::cache_path(&file);
    let mut bytes = fs::read(&path).expect("read cache");
    let stale = rustledger_loader::cache::CACHE_VERSION
        .checked_sub(1)
        .expect("CACHE_VERSION >= 1");
    bytes[8..12].copy_from_slice(&stale.to_le_bytes());
    fs::write(&path, &bytes).expect("write cache");

    assert!(
        rustledger_loader::load_cache_entry(&file).is_none(),
        "a cache blob one version behind must be refused, not reinterpreted",
    );
    rustledger_loader::invalidate_cache(&file);
}
