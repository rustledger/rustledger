//! The options reference must list every option the loader knows (#2925
//! review): `docs/reference/options.md` had dropped `use_precise_interpolation`
//! and `insert_pythonpath` from its "All Options" table.

use std::path::Path;

#[test]
fn test_options_reference_lists_every_known_option() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../docs/reference/options.md");
    let docs = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let table: Vec<&str> = docs
        .split("## All Options")
        .nth(1)
        .expect("options.md has an \"All Options\" section")
        .split("\n## ")
        .next()
        .unwrap_or_default()
        .lines()
        .filter_map(|line| line.strip_prefix("| `"))
        .filter_map(|rest| rest.split('`').next())
        .collect();

    let missing: Vec<&str> = rustledger_loader::known_options()
        .iter()
        .copied()
        .filter(|name| !table.contains(name))
        .collect();
    assert!(
        missing.is_empty(),
        "options the loader knows but the All Options table omits: {missing:?}"
    );
    let unknown: Vec<&str> = table
        .iter()
        .copied()
        .filter(|name| !rustledger_loader::known_options().contains(name))
        .collect();
    assert!(
        unknown.is_empty(),
        "the All Options table lists options the loader does not know: {unknown:?}"
    );
}
