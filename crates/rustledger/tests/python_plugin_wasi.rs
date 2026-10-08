//! End-to-end coverage for Python plugins run through the CPython-on-WASI
//! runtime (#2500): `rledger check` / `rledger query` on a ledger whose
//! `plugin "x.py"` directive names a real plugin file.
//!
//! Before #2500 no test ran a Python plugin through `PythonRuntime`; the
//! other Python tests run the compat layer under the host's `python3`. So
//! plugins could not run at all on main (a fuel budget too small for
//! `CPython` to start, and entry points looked up by the literal name
//! `plugin` instead of `__plugins__`) while CI stayed green.
//!
//! These tests need the `CPython` WASI runtime, which `rledger` downloads
//! and caches on first use (`python/download.rs`). Where it cannot be
//! fetched (the offline nix build sandbox) they skip with
//! [`SKIP_MARKER`]; the `python-gated-cargo-tests` CI job sets
//! `RLEDGER_REQUIRE_PYTHON_WASI=1`, which turns the skip into a failure,
//! and greps its log for the marker as well, so they cannot skip there.
#![cfg(feature = "python-plugin-wasm")]

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

/// Printed when the runtime is unavailable; CI fails on it.
const SKIP_MARKER: &str = "Skipping: CPython WASI runtime unavailable";

/// What a fuel trap reads like.
const TRAP: &str = "all fuel consumed";

const PASSTHROUGH: &str = "__plugins__ = ['passthrough']\n\
    def passthrough(entries, options_map):\n    return entries, []\n";

struct Run {
    out: String,
    success: bool,
}

/// Run `rledger <args>` in `dir`, with `dir` as the only config source.
fn run(bin: &Path, dir: &Path, args: &[&str]) -> Run {
    let output = Command::new(bin)
        .args(args)
        .current_dir(dir)
        .env("RLEDGER_CONFIG_DIR", dir)
        .env("PROGRAMDATA", dir)
        .output()
        .expect("run rledger");
    Run {
        out: format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ),
        success: output.status.success(),
    }
}

/// Write `plugin.py` and a ledger that loads it into a fresh temp dir.
/// `directive` is the `plugin` line.
fn setup(plugin: &str, directive: &str) -> (tempfile::TempDir, PathBuf) {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("plugin.py"), plugin).unwrap();
    let ledger = dir.path().join("ledger.beancount");
    std::fs::write(
        &ledger,
        format!(
            "{directive}\n\n\
             2024-01-01 open Assets:Bank USD\n\
             2024-01-01 open Income:Salary USD\n\n\
             2024-01-02 * \"Pay\" \"Salary \\\"quoted\\\" back\\\\slash\"\n  \
               Assets:Bank   10 USD\n  \
               Income:Salary\n"
        ),
    )
    .unwrap();
    (dir, ledger)
}

/// The `rledger` binary, or `None` (after printing [`SKIP_MARKER`]) when
/// the `CPython` runtime cannot be made available.
///
/// The first call runs one passthrough plugin, so the one-time download
/// and compile happen once, not in every parallel test at the same time
/// (the download writes to one fixed temp file).
fn rledger_with_python() -> Option<PathBuf> {
    static READY: OnceLock<Option<PathBuf>> = OnceLock::new();
    let ready = READY.get_or_init(|| {
        let bin = common::rledger_binary().expect("rledger binary");
        let (dir, ledger) = setup(PASSTHROUGH, "plugin \"plugin.py\"");
        let r = run(&bin, dir.path(), &["check", ledger.to_str().unwrap()]);
        if r.out.contains("Python runtime unavailable") {
            assert!(
                std::env::var_os("RLEDGER_REQUIRE_PYTHON_WASI").is_none(),
                "RLEDGER_REQUIRE_PYTHON_WASI is set but the CPython WASI runtime \
                 is unavailable:\n{}",
                r.out
            );
            return None;
        }
        Some(bin)
    });
    if ready.is_none() {
        eprintln!("{SKIP_MARKER}");
    }
    ready.clone()
}

/// `rledger query <ledger> <q>` output.
fn query(bin: &Path, dir: &Path, ledger: &Path, q: &str) -> Run {
    run(bin, dir, &["query", ledger.to_str().unwrap(), q])
}

#[test]
fn passthrough_plugin_runs() {
    let Some(bin) = rledger_with_python() else {
        return;
    };
    let (dir, ledger) = setup(PASSTHROUGH, "plugin \"plugin.py\"");
    let r = run(&bin, dir.path(), &["check", ledger.to_str().unwrap()]);
    assert!(r.success, "{}", r.out);
    assert!(r.out.contains("No errors found"), "{}", r.out);
    // A narration with a quote and a backslash survives the round trip.
    let q = query(&bin, dir.path(), &ledger, "SELECT narration");
    assert!(q.success, "{}", q.out);
    assert!(q.out.contains(r#"Salary "quoted" back\slash"#), "{}", q.out);
}

#[test]
fn plugin_modifies_an_entry() {
    let Some(bin) = rledger_with_python() else {
        return;
    };
    let plugin = "\
__plugins__ = ['shout']

def shout(entries, options_map):
    out = []
    for entry in entries:
        if isinstance(entry, Transaction):
            entry = entry._replace(narration=entry.narration.upper())
        out.append(entry)
    return out, []
";
    let (dir, ledger) = setup(plugin, "plugin \"plugin.py\"");
    let q = query(&bin, dir.path(), &ledger, "SELECT narration");
    assert!(q.success, "{}", q.out);
    assert!(q.out.contains(r#"SALARY "QUOTED" BACK\SLASH"#), "{}", q.out);
}

/// Every item of `__plugins__` runs, in order, each on the previous one's
/// output; a string names a function, anything else is the callable.
#[test]
fn plugins_list_runs_in_order() {
    let Some(bin) = rledger_with_python() else {
        return;
    };
    let plugin = "\
def _append(entries, suffix):
    return [e._replace(narration=e.narration + suffix) if isinstance(e, Transaction) else e
            for e in entries]

def first(entries, options_map):
    return _append(entries, ' -first'), []

def second(entries, options_map):
    return _append(entries, ' -second'), []

__plugins__ = ['first', second]
";
    let (dir, ledger) = setup(plugin, "plugin \"plugin.py\"");
    let q = query(&bin, dir.path(), &ledger, "SELECT narration");
    assert!(q.success, "{}", q.out);
    assert!(q.out.contains("back\\slash -first -second"), "{}", q.out);
}

/// The directive's config string is the third argument; without one, the
/// function gets two (beancount's `args = () if config is None`).
#[test]
fn config_string_is_passed_through() {
    let Some(bin) = rledger_with_python() else {
        return;
    };
    let plugin = "\
__plugins__ = ['configured']

def configured(entries, options_map, config='<no config>'):
    return [e._replace(narration=config) if isinstance(e, Transaction) else e
            for e in entries], []
";
    let (dir, ledger) = setup(plugin, r#"plugin "plugin.py" "it's \"set\"""#);
    let q = query(&bin, dir.path(), &ledger, "SELECT narration");
    assert!(q.success, "{}", q.out);
    assert!(q.out.contains(r#"it's "set""#), "{}", q.out);

    let (dir, ledger) = setup(plugin, "plugin \"plugin.py\"");
    let q = query(&bin, dir.path(), &ledger, "SELECT narration");
    assert!(q.success, "{}", q.out);
    assert!(q.out.contains("<no config>"), "{}", q.out);
}

/// No `__plugins__`: nothing runs (as in beancount, which skips the module
/// silently), and rledger says so with a warning. A function named
/// `plugin` is not an entry point.
#[test]
fn missing_plugins_list_runs_nothing_and_warns() {
    let Some(bin) = rledger_with_python() else {
        return;
    };
    let plugin = "\
def plugin(entries, options_map):
    raise RuntimeError('must not run')
";
    let (dir, ledger) = setup(plugin, "plugin \"plugin.py\"");
    let r = run(&bin, dir.path(), &["check", ledger.to_str().unwrap()]);
    assert!(r.success, "a warning must not fail the check:\n{}", r.out);
    assert!(
        r.out
            .contains(r#"warning[PLUGIN]: Python plugin "plugin.py" has no __plugins__"#),
        "{}",
        r.out
    );
    assert!(!r.out.contains("must not run"), "{}", r.out);
}

/// A listed name the module does not define is an error naming it, and
/// nothing in the module runs (beancount aborts the load with an
/// `AttributeError`).
#[test]
fn listed_but_undefined_name_is_an_error() {
    let Some(bin) = rledger_with_python() else {
        return;
    };
    let plugin = "\
__plugins__ = ['shout', 'missing']

def shout(entries, options_map):
    return [e._replace(narration='SHOUTED') if isinstance(e, Transaction) else e
            for e in entries], []
";
    let (dir, ledger) = setup(plugin, "plugin \"plugin.py\"");
    let r = run(&bin, dir.path(), &["check", ledger.to_str().unwrap()]);
    assert!(!r.success, "{}", r.out);
    assert!(
        r.out.contains(
            r#"error[PLUGIN]: __plugins__ of Python plugin "plugin.py" lists "missing", which the plugin does not define"#
        ),
        "{}",
        r.out
    );
    let q = query(&bin, dir.path(), &ledger, "SELECT narration");
    assert!(!q.out.contains("SHOUTED"), "{}", q.out);
}

/// The host's time budget governs Python plugins. The plugin burns about
/// 7G fuel (5M loop iterations at ~1.1k fuel each, plus ~1.2G of `CPython`
/// startup, measured), which fits the default 30-second budget (30G) and
/// traps on a 3-second one (3G), where a passthrough plugin still runs.
#[test]
fn host_time_budget_applies_to_python_plugins() {
    let Some(bin) = rledger_with_python() else {
        return;
    };
    let burn = "\
__plugins__ = ['burn']

def burn(entries, options_map):
    n = 0
    for i in range(5_000_000):
        n += i
    return entries, []
";
    let (dir, ledger) = setup(burn, "plugin \"plugin.py\"");
    let ledger = ledger.to_str().unwrap();

    let fits = run(&bin, dir.path(), &["check", ledger]);
    assert!(
        fits.success,
        "the default budget must cover it:\n{}",
        fits.out
    );

    let tight = run(
        &bin,
        dir.path(),
        &["--plugin-max-time-secs", "3", "check", ledger],
    );
    assert!(!tight.success, "{}", tight.out);
    assert!(tight.out.contains(TRAP), "{}", tight.out);
    assert!(
        tight.out.contains("exceeded its 3-second time budget"),
        "the trap must name the budget that ran out:\n{}",
        tight.out
    );

    // The config file sets it too.
    std::fs::write(
        dir.path().join("config.toml"),
        "[plugins]\nmax_time_secs = 3\n",
    )
    .unwrap();
    let configured = run(&bin, dir.path(), &["check", ledger]);
    assert!(configured.out.contains(TRAP), "{}", configured.out);

    // ...and 3 seconds is enough for CPython to start and run a small plugin.
    let (dir, ledger) = setup(PASSTHROUGH, "plugin \"plugin.py\"");
    let small = run(
        &bin,
        dir.path(),
        &[
            "--plugin-max-time-secs",
            "3",
            "check",
            ledger.to_str().unwrap(),
        ],
    );
    assert!(small.success, "{}", small.out);
}
