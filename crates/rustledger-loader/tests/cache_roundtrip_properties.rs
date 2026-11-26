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

/// The cache settings these properties run under: none, whatever the
/// developer's environment holds. The `*_in` functions take the settings
/// instead of reading process env, so an inherited
/// `BEANCOUNT_LOAD_CACHE_FILENAME` cannot redirect these writes out of the
/// fixture, and the tests need no precondition on the environment (#1729).
fn no_env() -> rustledger_loader::CacheEnv {
    rustledger_loader::CacheEnv::default()
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
            includes: Vec::new(),
        };
        rustledger_loader::save_cache_entry_in(&file, &entry, &no_env()).expect("save");
        let back = rustledger_loader::load_cache_entry_in(&file, &no_env()).expect("load cache");

        assert_eq!(
            format!("{:?}", back.directives),
            format!("{:?}", entry.directives),
            "{name}: directives did not survive the cache round-trip",
        );
        rustledger_loader::invalidate_cache_in(&file, &no_env());
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
        includes: Vec::new(),
    };
    rustledger_loader::save_cache_entry_in(&file, &entry, &no_env()).expect("save");

    // Rewrite the version word in the header to the previous version.
    let path = rustledger_loader::cache_path_in(&file, &no_env());
    let mut bytes = fs::read(&path).expect("read cache");
    let stale = rustledger_loader::cache::CACHE_VERSION
        .checked_sub(1)
        .expect("CACHE_VERSION >= 1");
    bytes[8..12].copy_from_slice(&stale.to_le_bytes());
    fs::write(&path, &bytes).expect("write cache");

    assert!(
        rustledger_loader::load_cache_entry_in(&file, &no_env()).is_none(),
        "a cache blob one version behind must be refused, not reinterpreted",
    );
    rustledger_loader::invalidate_cache_in(&file, &no_env());
}

/// Archive a fresh load as `rledger`'s `loadcache` does, then restore it.
fn cache_round_trip(file: &std::path::Path) -> rustledger_loader::LoadResult {
    let loaded = rustledger_loader::Loader::new().load(file).expect("load");
    let entry = rustledger_loader::CacheEntry {
        directives: loaded.directives.clone(),
        options: rustledger_loader::CachedOptions::from(&loaded.options),
        plugins: Vec::new(),
        files: loaded
            .source_map
            .files()
            .iter()
            .map(|f| f.opened_path.to_string_lossy().into_owned())
            .collect(),
        includes: loaded.source_map.include_lists(),
    };
    rustledger_loader::save_cache_entry_in(file, &entry, &no_env()).expect("save");
    let back = rustledger_loader::load_cache_entry_in(file, &no_env()).expect("load cache");
    rustledger_loader::invalidate_cache_in(file, &no_env());
    back.into_load_result()
}

/// A cache hit must report the option warnings a fresh load reports: the same
/// codes, messages and sites, in the same order (#3002). Before, a load with
/// any option warning was never cached, so an included file's `option
/// "title"` (E7009) made every run re-parse.
///
/// Covers both kinds: the warnings raised while setting options, which the
/// cache archives (E7001, E7003, E7009), and the post-load ones a hit
/// re-derives (E7006, E7010). A code added to one kind without the other
/// (`POST_LOAD_OPTION_CODES`) duplicates or drops a warning here.
#[test]
fn test_into_load_result_replays_option_warnings() {
    let dir = fixture_dir();
    let file = dir.path().join("main.beancount");
    fs::write(
        &file,
        "option \"title\" \"Main\"\n\
         option \"title\" \"Main again\"\n\
         option \"no_such_option\" \"x\"\n\
         option \"documents\" \"missing-docs\"\n\
         option \"account_previous_balances\" \"Equity:Opening\"\n\
         include \"child.beancount\"\n",
    )
    .expect("write main");
    fs::write(
        dir.path().join("child.beancount"),
        "option \"title\" \"Child\"\n2020-01-01 open Assets:Cash\n",
    )
    .expect("write child");

    let fresh = rustledger_loader::Loader::new().load(&file).expect("load");
    let codes: Vec<&str> = fresh.options.warnings.iter().map(|w| w.code).collect();
    for code in ["E7001", "E7003", "E7006", "E7009", "E7010"] {
        assert!(
            codes.contains(&code),
            "fixture no longer raises {code}: {codes:?}"
        );
    }
    assert!(
        fresh.options.warnings.iter().all(|w| w.site.is_some()),
        "every warning here has an `option` line to point at: {:?}",
        fresh.options.warnings
    );

    let hit = cache_round_trip(&file);
    assert_eq!(
        hit.options.warnings, fresh.options.warnings,
        "a cache hit must report exactly the option warnings of a fresh load"
    );
}

/// E7006 asks the filesystem, not the source, so a hit re-derives it rather
/// than replaying the archived answer: creating the missing documents root
/// after the cache was written must clear it, as it clears a fresh load.
#[test]
fn test_into_load_result_rederives_document_root_warning() {
    let dir = fixture_dir();
    let file = dir.path().join("main.beancount");
    fs::write(
        &file,
        "option \"documents\" \"docs\"\n2020-01-01 open Assets:Cash\n",
    )
    .expect("write main");

    let loaded = rustledger_loader::Loader::new().load(&file).expect("load");
    assert_eq!(
        loaded
            .options
            .warnings
            .iter()
            .map(|w| w.code)
            .collect::<Vec<_>>(),
        ["E7006"],
    );
    let entry = rustledger_loader::CacheEntry {
        directives: loaded.directives.clone(),
        options: rustledger_loader::CachedOptions::from(&loaded.options),
        plugins: Vec::new(),
        files: vec![file.to_string_lossy().into_owned()],
        includes: Vec::new(),
    };
    rustledger_loader::save_cache_entry_in(&file, &entry, &no_env()).expect("save");

    fs::create_dir(dir.path().join("docs")).expect("create docs");
    let hit = rustledger_loader::load_cache_entry_in(&file, &no_env())
        .expect("load cache")
        .into_load_result();
    let fresh = rustledger_loader::Loader::new().load(&file).expect("load");
    assert!(
        fresh.options.warnings.is_empty(),
        "{:?}",
        fresh.options.warnings
    );
    assert_eq!(hit.options.warnings, fresh.options.warnings);
    rustledger_loader::invalidate_cache_in(&file, &no_env());
}
