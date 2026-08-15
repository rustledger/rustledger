#![no_main]
//! Differential fuzz target for the green transaction conversion (the
//! lossless-CST-tax removal). The green-wired `parse` must produce output
//! **byte-identical** to the pure-red path on every input: the green
//! transaction converter returns `Some` only when it exactly replicates red,
//! and bails to red otherwise — so any divergence here is a green-path bug.
use libfuzzer_sys::fuzz_target;
use rustledger_parser::cst::parse_red_only;
use rustledger_parser::parse;

fuzz_target!(|data: &[u8]| {
    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };
    let green = parse(src);
    let red = parse_red_only(src);

    // Compare the full result via Debug (avoids requiring `PartialEq` on every
    // field type). Directives + errors are where a green divergence would show.
    assert_eq!(
        format!("{:?}", green.directives),
        format!("{:?}", red.directives),
        "green vs red directives diverged"
    );
    assert_eq!(
        format!("{:?}", green.errors),
        format!("{:?}", red.errors),
        "green vs red errors diverged"
    );
    assert_eq!(
        format!("{:?}", green.options),
        format!("{:?}", red.options),
        "green vs red options diverged"
    );
    assert_eq!(
        format!("{:?}", green.comments),
        format!("{:?}", red.comments),
        "green vs red comments diverged"
    );
    // Occurrences come from the green walk_descendants pass.
    assert_eq!(
        format!("{:?}", green.account_occurrences),
        format!("{:?}", red.account_occurrences),
        "green vs red account_occurrences diverged"
    );
    assert_eq!(
        format!("{:?}", green.currency_occurrences),
        format!("{:?}", red.currency_occurrences),
        "green vs red currency_occurrences diverged"
    );
    // The remaining ParseResult observables. The green conversion doesn't
    // produce these today (they come from the shared top-level walk), so
    // they hold trivially — the assertions pin that: if the green path ever
    // grows to touch includes/plugins/warnings/BOM/alignment, any divergence
    // surfaces here instead of shipping unpinned.
    assert_eq!(
        green.includes, red.includes,
        "green vs red includes diverged"
    );
    assert_eq!(
        green.plugins, red.plugins,
        "green vs red plugins diverged"
    );
    assert_eq!(
        format!("{:?}", green.warnings),
        format!("{:?}", red.warnings),
        "green vs red warnings diverged"
    );
    assert_eq!(
        green.has_leading_bom, red.has_leading_bom,
        "green vs red has_leading_bom diverged"
    );
    // `alignment()` rather than the field: it is a lazily-computed `OnceLock`
    // now. Asking here is what this target wants anyway — it must compare the
    // VALUE the two paths produce, and forcing it on both is the only way to
    // do that.
    assert_eq!(
        green.alignment(),
        red.alignment(),
        "green vs red alignment diverged"
    );
});
