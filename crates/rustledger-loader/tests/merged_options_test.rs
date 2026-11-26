//! The options beancount merges across included files come out in its
//! breadth-first parse order (#3038).
//!
//! beancount 3.2.3 parses the top-level file, then its includes breadth
//! first (`loader._parse_recursive`), and `loader.aggregate_options_map`
//! merges `operating_currency` in that order, each currency once, and
//! `display_precision` through `DisplayContext::update_from`, which keeps the
//! top-level file's fixed precision. The loader reads depth first and
//! applied both in that order, keeping repeats and letting an included
//! file's precision override the top-level file's. Every expected value
//! here is what `beancount.loader.load_file` gives for the same tree.

use rustledger_loader::{
    CacheEntry, CacheEnv, CachedOptions, LoadResult, Loader, VirtualFileSystem,
    load_cache_entry_in, save_cache_entry_in,
};
use std::path::Path;

fn load_vfs(files: &[(&str, &str)]) -> LoadResult {
    let mut vfs = VirtualFileSystem::new();
    for (name, text) in files {
        vfs.add_file(name, *text);
    }
    let result = Loader::new()
        .with_filesystem(Box::new(vfs))
        .load(Path::new(files[0].0))
        .expect("loads");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    result
}

/// The issue's tree: `main` sets `MMM` and includes `x` then `y`; `x` sets
/// `XXX` and includes `z` (`ZZZ`); `y` sets `YYY`. beancount gives
/// `[MMM, XXX, YYY, ZZZ]`; the loader gave `[MMM, XXX, ZZZ, YYY]`.
const NESTED: &[(&str, &str)] = &[
    (
        "main.beancount",
        "option \"operating_currency\" \"MMM\"\ninclude \"x.beancount\"\ninclude \"y.beancount\"\n",
    ),
    (
        "x.beancount",
        "option \"operating_currency\" \"XXX\"\ninclude \"z.beancount\"\n",
    ),
    ("z.beancount", "option \"operating_currency\" \"ZZZ\"\n"),
    ("y.beancount", "option \"operating_currency\" \"YYY\"\n"),
];

#[test]
fn test_load_operating_currency_merges_breadth_first() {
    let result = load_vfs(NESTED);
    assert_eq!(
        result.options.operating_currency,
        ["MMM", "XXX", "YYY", "ZZZ"]
    );
}

/// A currency named again, in the same file or another, keeps its first
/// place. `main` names `USD` twice, includes `a`, then names `EUR`; `a`
/// names `USD`, `GBP`, `EUR`. beancount gives `[USD, EUR, GBP]` (a file's
/// options all come before its includes'); the loader gave
/// `[USD, USD, EUR, USD, GBP, EUR]`.
#[test]
fn test_load_operating_currency_drops_repeats() {
    let result = load_vfs(&[
        (
            "main.beancount",
            "option \"operating_currency\" \"USD\"\noption \"operating_currency\" \"USD\"\n\
             include \"a.beancount\"\noption \"operating_currency\" \"EUR\"\n",
        ),
        (
            "a.beancount",
            "option \"operating_currency\" \"USD\"\noption \"operating_currency\" \"GBP\"\n\
             option \"operating_currency\" \"EUR\"\n",
        ),
    ]);
    assert_eq!(result.options.operating_currency, ["USD", "EUR", "GBP"]);
}

/// A file included twice takes its place from the include breadth first
/// meets first (`SourceMap::parse_ranks`): `main` includes `a` then `b`,
/// `a` includes `c`, and `c` includes `b` (where the loader reads it, depth
/// first). beancount parses `main, a, b, c`: `[AAA, BBB, CCC]`.
#[test]
fn test_load_operating_currency_follows_a_duplicate_include() {
    let result = Loader::new()
        .with_filesystem(Box::new({
            let mut vfs = VirtualFileSystem::new();
            vfs.add_file(
                "main.beancount",
                "include \"a.beancount\"\ninclude \"b.beancount\"\n",
            );
            vfs.add_file(
                "a.beancount",
                "option \"operating_currency\" \"AAA\"\ninclude \"c.beancount\"\n",
            );
            vfs.add_file("b.beancount", "option \"operating_currency\" \"BBB\"\n");
            vfs.add_file(
                "c.beancount",
                "include \"b.beancount\"\noption \"operating_currency\" \"CCC\"\n",
            );
            vfs
        }))
        .load(Path::new("main.beancount"))
        .expect("loads");
    // The duplicate include of `b` is reported, as bean-check reports it.
    assert_eq!(result.errors.len(), 1, "{:?}", result.errors);
    assert_eq!(result.options.operating_currency, ["AAA", "BBB", "CCC"]);
}

/// `display_precision` in the top-level file wins over an included file's,
/// and the display context reads the merged value: bean-query renders
/// `1.23456 USD` as `1.23 USD` here, where rledger rendered `1.235 USD`.
#[test]
fn test_load_display_precision_top_level_wins() {
    let result = load_vfs(&[
        (
            "main.beancount",
            "option \"display_precision\" \"USD:0.01\"\ninclude \"a.beancount\"\n\
             2020-01-01 open Assets:A\n2020-01-01 open Assets:B\n\
             2020-01-02 * \"x\"\n  Assets:A  1.23456 USD\n  Assets:B\n",
        ),
        (
            "a.beancount",
            "option \"display_precision\" \"USD:0.001\"\n",
        ),
    ]);
    assert_eq!(result.options.display_precision.get("USD"), Some(&2));
    assert_eq!(result.display_context.get_precision("USD"), Some(2));
}

/// A tree read from disk, where sibling includes (a glob's matches) are
/// read in parallel: the merge does not depend on how the files were read.
/// `main` includes `g/*.beancount` (`p` including `../z`, and `q`) and then
/// `y`. The loader takes a glob's matches sorted, so it parses
/// `main, p, q, y, z`; beancount takes them in `glob.glob`'s directory order,
/// which is not specified (`q, p` on one filesystem), and the rest the same:
/// `y` after both matches, and `z`, which `p` includes, last.
#[test]
fn test_load_operating_currency_from_disk_with_a_glob() {
    let dir = tempfile::tempdir().expect("temp dir");
    std::fs::create_dir(dir.path().join("g")).expect("mkdir");
    for (name, text) in [
        (
            "main.beancount",
            "include \"g/*.beancount\"\ninclude \"y.beancount\"\n",
        ),
        (
            "g/p.beancount",
            "option \"operating_currency\" \"PPP\"\ninclude \"../z.beancount\"\n",
        ),
        ("g/q.beancount", "option \"operating_currency\" \"QQQ\"\n"),
        ("y.beancount", "option \"operating_currency\" \"YYY\"\n"),
        ("z.beancount", "option \"operating_currency\" \"ZZZ\"\n"),
    ] {
        std::fs::write(dir.path().join(name), text).expect("write");
    }
    let result = Loader::new()
        .load(&dir.path().join("main.beancount"))
        .expect("loads");
    assert!(result.errors.is_empty(), "{:?}", result.errors);
    assert_eq!(
        result.options.operating_currency,
        ["PPP", "QQQ", "YYY", "ZZZ"]
    );
}

/// A parse-cache hit gives the merged values the load gave: the cache
/// archives the merged options, as `rledger`'s `load_result_cached` writes
/// them.
#[test]
fn test_cache_hit_keeps_the_merged_options() {
    let dir = tempfile::tempdir().expect("temp dir");
    for (name, text) in NESTED {
        std::fs::write(dir.path().join(name), text).expect("write");
    }
    std::fs::write(
        dir.path().join("y.beancount"),
        "option \"operating_currency\" \"YYY\"\noption \"display_precision\" \"USD:0.001\"\n",
    )
    .expect("write");
    let main = dir.path().join("main.beancount");
    std::fs::write(
        &main,
        "option \"operating_currency\" \"MMM\"\noption \"display_precision\" \"USD:0.01\"\n\
         include \"x.beancount\"\ninclude \"y.beancount\"\n",
    )
    .expect("write");

    let cold = Loader::new().load(&main).expect("loads");
    assert!(cold.errors.is_empty(), "{:?}", cold.errors);
    let entry = CacheEntry {
        directives: cold.directives.clone(),
        options: CachedOptions::from(&cold.options),
        plugins: Vec::new(),
        files: cold
            .source_map
            .files()
            .iter()
            .map(|f| f.opened_path.to_string_lossy().into_owned())
            .collect(),
        includes: cold.source_map.include_lists(),
    };
    let env = CacheEnv::default();
    save_cache_entry_in(&main, &entry, &env).expect("save");
    let warm = load_cache_entry_in(&main, &env)
        .expect("cache hit")
        .into_load_result();

    for (run, result) in [("cold", &cold), ("warm", &warm)] {
        assert_eq!(
            result.options.operating_currency,
            ["MMM", "XXX", "YYY", "ZZZ"],
            "{run}"
        );
        assert_eq!(
            result.options.display_precision.get("USD"),
            Some(&2),
            "{run}"
        );
    }
}
