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
});
