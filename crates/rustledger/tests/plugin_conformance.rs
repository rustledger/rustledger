//! Plugin conformance matrix: every plugin kind through every user entry
//! point, asserting the plugin's EFFECT in each command's output (a
//! diagnostic it reports, a tag it adds, a transaction it imports), never
//! just an exit code (#2500 review).
//!
//! | Kind | Entry point | Commands |
//! |---|---|---|
//! | native | `plugin "check_commodity"` / `"auto_tag"` directives | check, query, report |
//! | native | `check --native-plugin check_commodity` | check |
//! | native | a `beancount.plugins.*` name resolves native, not Python | check |
//! | WASM (a `wasm_plugin_main!` guest) | `plugin "x.wasm"` directive | check, query, report |
//! | WASM | `check --plugin x.wasm` | check |
//! | Python file | `plugin "x.py"` (fixtures in `tests/fixtures/python-plugins`) | check, query, report |
//! | Python file | `plugin "python:./x.py"` | check |
//! | Python module | `plugin "python:module"`: rejected by design (#1432) | check |
//! | Python built-in | `plugin "python:leafonly"` / `"python:check_commodity"` force the Python implementation | check |
//! | native + Python together | `with_plugins.beancount` fixture | check |
//! | WASM importer (a `wasm_importer_main!` guest) | `extract --wasm-importer x.wasm` | extract |
//!
//! And the LIMITS of each sandboxed kind (WASM plugin, Python plugin,
//! WASM importer), through the same commands:
//!
//! - the default time budget covers a realistic plugin (the effect cases);
//! - a tight budget, from `--plugin-max-time-secs` and from
//!   `[plugins] max_time_secs`, stops a plugin that never finishes, with a
//!   message naming the budget and how to raise it;
//! - a plugin that allocates past the 256 MiB sandbox cap is stopped with
//!   a memory error, and rledger itself survives to report it;
//! - isolation: a WASM guest cannot import anything (so no filesystem, no
//!   network); a Python plugin sees exactly `/lib` and `/work`, both
//!   read-only, and cannot reach the ledger's directory, `$HOME`,
//!   `/etc/passwd` or the network;
//! - a plugin's error is reported with its message and source location.
//!
//! Tool-gated: the WASM guests are built for `wasm32-unknown-unknown` by
//! this test (once), and the Python cases need the `CPython` WASI runtime.
//! Where either is missing the cases skip with a marker; the
//! `python-gated-cargo-tests` CI job sets `RLEDGER_REQUIRE_WASM32=1` and
//! `RLEDGER_REQUIRE_PYTHON_WASI=1`, which turn the skips into failures,
//! and greps its log for the markers.
#![cfg(feature = "python-plugin-wasm")]

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

/// Printed when the WASM guests cannot be built; CI fails on it.
const WASM_SKIP_MARKER: &str = "Skipping: conformance WASM guests unavailable";

/// Two transactions, one without a payee (for the Python `error_plugin`
/// fixture), posting to `Assets:Bank`, which has a child account (for
/// `leafonly`), in `USD`, which has no `commodity` directive (for
/// `check_commodity`).
const BODY: &str = "\
2024-01-01 open Assets:Bank USD
2024-01-01 open Assets:Bank:Sub USD
2024-01-01 open Expenses:Food USD

2024-01-02 * \"Shop\" \"Lunch\"
  Assets:Bank  -10 USD
  Expenses:Food

2024-01-03 * \"Snack\"
  Assets:Bank  -2 USD
  Expenses:Food
";

/// Line of the payee-less transaction in a ledger of a one-line header,
/// a blank line, and [`BODY`].
const SNACK_LINE: usize = 11;

struct Out {
    text: String,
    code: Option<i32>,
}

impl Out {
    #[track_caller]
    fn has(&self, needle: &str) -> &Self {
        assert!(
            self.text.contains(needle),
            "expected {needle:?} in the output:\n{}",
            self.text
        );
        self
    }

    #[track_caller]
    fn lacks(&self, needle: &str) -> &Self {
        assert!(
            !self.text.contains(needle),
            "did not expect {needle:?} in the output:\n{}",
            self.text
        );
        self
    }

    /// rledger reported a failure and exited normally (not killed).
    #[track_caller]
    fn failed_cleanly(&self) -> &Self {
        assert_eq!(self.code, Some(1), "{}", self.text);
        self
    }
}

fn bin() -> PathBuf {
    common::rledger_binary().expect("rledger binary")
}

/// Run `rledger <args>` in `dir`, with `dir` as the only config source.
fn run(dir: &Path, args: &[&str]) -> Out {
    run_env(dir, args, &[])
}

/// [`run`] with extra environment variables.
fn run_env(dir: &Path, args: &[&str], env: &[(&str, &Path)]) -> Out {
    let mut command = Command::new(bin());
    command
        .args(args)
        .current_dir(dir)
        .env("RLEDGER_CONFIG_DIR", dir)
        .env("PROGRAMDATA", dir);
    for (key, value) in env {
        command.env(key, value);
    }
    let output = command.output().expect("run rledger");
    Out {
        text: format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ),
        code: output.status.code(),
    }
}

/// A temp dir holding `ledger.beancount` = `header`, a blank line, [`BODY`].
fn ledger(header: &str) -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("ledger.beancount"),
        format!("{header}\n\n{BODY}"),
    )
    .unwrap();
    dir
}

/// `check`, `query` and `report`, the three commands that run a ledger's
/// plugins, on `dir/ledger.beancount`.
fn all_commands(dir: &Path) -> [(&'static str, Out); 3] {
    [
        ("check", run(dir, &["check", "ledger.beancount"])),
        (
            "query",
            run(
                dir,
                &["query", "ledger.beancount", "SELECT date, narration, tags"],
            ),
        ),
        (
            "report",
            run(dir, &["report", "ledger.beancount", "journal"]),
        ),
    ]
}

// ---------------------------------------------------------------------------
// Tool gates
// ---------------------------------------------------------------------------

/// The built conformance guests: (directive plugin, importer).
struct Guests {
    plugin: PathBuf,
    importer: PathBuf,
}

/// Build `tests/fixtures/conformance` for wasm32 once per test binary, or
/// `None` (after printing [`WASM_SKIP_MARKER`]) when that is impossible
/// here; with `RLEDGER_REQUIRE_WASM32` set, panic instead.
fn guests() -> Option<&'static Guests> {
    static GUESTS: OnceLock<Option<Guests>> = OnceLock::new();
    let guests = GUESTS.get_or_init(|| {
        let manifest =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/conformance/Cargo.toml");
        let target = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("conformance-guests");
        // Scrub what the outer build set that does not apply to a wasm32
        // build (as the fixture build scripts in rustledger-plugin and
        // rustledger-importer do).
        let output = Command::new(env!("CARGO"))
            .env_remove("RUSTFLAGS")
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .env_remove("CARGO_BUILD_RUSTFLAGS")
            .env_remove("CARGO_BUILD_TARGET")
            .env_remove("RUSTDOCFLAGS")
            .env_remove("CARGO_INCREMENTAL")
            .env_remove("LLVM_PROFILE_FILE")
            .args([
                "--config",
                "target.wasm32-unknown-unknown.rustflags=[]",
                "build",
                "--release",
                "--target",
                "wasm32-unknown-unknown",
                "--manifest-path",
            ])
            .arg(&manifest)
            .arg("--target-dir")
            .arg(&target)
            .output();
        let release = target.join("wasm32-unknown-unknown/release");
        let built = Guests {
            plugin: release.join("conformance_wasm_plugin.wasm"),
            importer: release.join("conformance_wasm_importer.wasm"),
        };
        match output {
            Ok(out) if out.status.success() && built.plugin.exists() && built.importer.exists() => {
                Some(built)
            }
            other => {
                let why = match other {
                    Ok(out) => String::from_utf8_lossy(&out.stderr).into_owned(),
                    Err(e) => e.to_string(),
                };
                assert!(
                    std::env::var_os("RLEDGER_REQUIRE_WASM32").is_none(),
                    "RLEDGER_REQUIRE_WASM32 is set but the conformance WASM guests did \
                     not build:\n{why}"
                );
                eprintln!("{WASM_SKIP_MARKER}: {why}");
                None
            }
        }
    });
    if guests.is_none() {
        eprintln!("{WASM_SKIP_MARKER}");
    }
    guests.as_ref()
}

fn python_ready() -> bool {
    common::python_wasi_ready(&bin())
}

/// Copy the WASM directive plugin into `dir` as `conformance.wasm`.
fn install_wasm_plugin(dir: &Path, guests: &Guests) {
    std::fs::copy(&guests.plugin, dir.join("conformance.wasm")).unwrap();
}

/// Copy the `tests/fixtures/python-plugins` files into `dir`.
fn install_python_fixtures(dir: &Path) {
    let fixtures = common::project_root().join("tests/fixtures/python-plugins");
    for entry in std::fs::read_dir(fixtures).unwrap() {
        let path = entry.unwrap().path();
        std::fs::copy(&path, dir.join(path.file_name().unwrap())).unwrap();
    }
}

// ---------------------------------------------------------------------------
// Native
// ---------------------------------------------------------------------------

#[test]
fn native_directive_in_check_query_report() {
    let dir = ledger("plugin \"check_commodity\"\nplugin \"auto_tag\"");
    for (cmd, out) in all_commands(dir.path()) {
        out.has("commodity 'USD' used but not declared");
        if cmd == "query" {
            out.has("food");
        }
    }
}

#[test]
fn native_flag_in_check() {
    let dir = ledger("");
    run(dir.path(), &["check", "ledger.beancount"]).lacks("not declared");
    run(
        dir.path(),
        &[
            "check",
            "--native-plugin",
            "check_commodity",
            "ledger.beancount",
        ],
    )
    .has("commodity 'USD' used but not declared");
}

/// `beancount.plugins.*` names resolve to the native plugins: no Python
/// runtime is started for them.
#[test]
fn native_is_preferred_for_beancount_plugin_names() {
    let dir = tempfile::tempdir().unwrap();
    install_python_fixtures(dir.path());
    run(dir.path(), &["check", "native_preferred.beancount"])
        .has("No errors found")
        .lacks("Python");
    let dir = ledger("plugin \"beancount.plugins.check_commodity\"");
    run(dir.path(), &["check", "ledger.beancount"])
        .has("commodity 'USD' used but not declared")
        .lacks("Python");
}

// ---------------------------------------------------------------------------
// WASM directive plugin
// ---------------------------------------------------------------------------

#[test]
fn wasm_directive_in_check_query_report() {
    let Some(guests) = guests() else { return };
    let dir = ledger("plugin \"conformance.wasm\"");
    install_wasm_plugin(dir.path(), guests);
    for (cmd, out) in all_commands(dir.path()) {
        out.has("conformance: WASM plugin ran over 5 directives");
        if cmd == "query" {
            out.has("conformance-wasm");
        }
    }
}

#[test]
fn wasm_flag_in_check() {
    let Some(guests) = guests() else { return };
    let dir = ledger("");
    install_wasm_plugin(dir.path(), guests);
    run(
        dir.path(),
        &["check", "--plugin", "conformance.wasm", "ledger.beancount"],
    )
    .has("conformance: WASM plugin ran over 5 directives");
}

// ---------------------------------------------------------------------------
// Python
// ---------------------------------------------------------------------------

#[test]
fn python_file_in_check_query_report() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"tag_plugin.py\"\nplugin \"error_plugin.py\"");
    install_python_fixtures(dir.path());
    let located = format!("ledger.beancount:{}", SNACK_LINE + 1);
    for (cmd, out) in all_commands(dir.path()) {
        out.has("Transaction on 2024-01-03 has no payee");
        if cmd == "check" {
            // The error is located at its entry (the header is two lines,
            // so the transaction is on line SNACK_LINE + 1).
            out.has(&located);
        }
        if cmd == "query" {
            out.has("food");
        }
    }
}

/// `python:` before a file path runs that file in Python.
#[test]
fn python_prefixed_file_in_check() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"python:./error_plugin.py\"");
    install_python_fixtures(dir.path());
    run(dir.path(), &["check", "ledger.beancount"]).has("Transaction on 2024-01-03 has no payee");
}

/// `python:module` is refused by design (#1432): the sandbox cannot see
/// the host's Python path, so a plugin is referenced by file.
#[test]
fn python_module_name_is_refused() {
    let dir = ledger("plugin \"python:my_company.plugins.tagger\"");
    run(dir.path(), &["check", "ledger.beancount"])
        .has("is not supported by module name; reference the file directly");
}

/// `python:<name>` for a built-in Python plugin runs the Python
/// implementation, whose messages are beancount's, instead of the native
/// one.
#[test]
fn python_prefix_forces_builtin_python_plugins() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"python:leafonly\"");
    run(dir.path(), &["check", "ledger.beancount"])
        .has("ledger.beancount:3:1: error[PLUGIN]: Non-leaf account 'Assets:Bank' has postings on it")
        .lacks("Posting to non-leaf account");
    let dir = ledger("plugin \"python:beancount.plugins.check_commodity\"");
    run(dir.path(), &["check", "ledger.beancount"])
        .has("Missing Commodity directive for 'USD' in 'Assets:Bank'")
        .lacks("used but not declared");
}

/// Native and Python plugins in one ledger (the `with_plugins` fixture):
/// each one's effect shows.
#[test]
fn native_and_python_together() {
    if !python_ready() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    install_python_fixtures(dir.path());
    run(dir.path(), &["check", "with_plugins.beancount"])
        .has("with_plugins.beancount:21:1: error[PLUGIN]: Transaction on 2020-01-15 has no payee")
        .has("Posting to non-leaf account 'Expenses:Food'");
}

/// What a plugin prints goes to stderr and leaves its result intact.
#[test]
fn python_print_reaches_stderr_without_corrupting_output() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"count_plugin.py\"");
    install_python_fixtures(dir.path());
    run(dir.path(), &["check", "ledger.beancount"])
        .has("Entry counts: {")
        .has("No errors found");
}

// ---------------------------------------------------------------------------
// WASM importer
// ---------------------------------------------------------------------------

fn extract(dir: &Path, guests: &Guests, content: &str, flags: &[&str]) -> Out {
    std::fs::copy(&guests.importer, dir.join("importer.wasm")).unwrap();
    std::fs::write(dir.join("statement.conformance"), content).unwrap();
    let mut args: Vec<&str> = flags.to_vec();
    args.extend([
        "extract",
        "--wasm-importer",
        "importer.wasm",
        "--account",
        "Assets:Bank",
        "statement.conformance",
    ]);
    run(dir, &args)
}

#[test]
fn wasm_importer_in_extract() {
    let Some(guests) = guests() else { return };
    let dir = tempfile::tempdir().unwrap();
    extract(dir.path(), guests, "statement", &[])
        .has("conformance: WASM importer ran")
        .has("2024-01-15 * \"conformance import\"")
        .has("Expenses:Conformance   12.34 USD");
}

// ---------------------------------------------------------------------------
// Limits: time budget
// ---------------------------------------------------------------------------

/// The budget message: names the budget and how to raise it.
fn budget(secs: u64) -> String {
    format!(
        "exceeded its {secs}-second time budget (rledger raises it with \
         --plugin-max-time-secs or [plugins] max_time_secs)"
    )
}

/// Run `f` with the budget set by the flag, then by the config file.
fn both_budget_sources(dir: &Path, secs: u64, f: impl Fn(&[&str]) -> Out) {
    let secs_str = secs.to_string();
    f(&["--plugin-max-time-secs", &secs_str])
        .failed_cleanly()
        .has(&budget(secs));
    std::fs::write(
        dir.join("config.toml"),
        format!("[plugins]\nmax_time_secs = {secs}\n"),
    )
    .unwrap();
    f(&[]).failed_cleanly().has(&budget(secs));
    std::fs::remove_file(dir.join("config.toml")).unwrap();
}

#[test]
fn wasm_plugin_time_budget() {
    let Some(guests) = guests() else { return };
    let dir = ledger("plugin \"conformance.wasm\" \"burn\"");
    install_wasm_plugin(dir.path(), guests);
    // The default (30 s) stops it too, and says so.
    run(dir.path(), &["check", "ledger.beancount"])
        .failed_cleanly()
        .has(&budget(30));
    both_budget_sources(dir.path(), 1, |flags| {
        let mut args = flags.to_vec();
        args.extend(["check", "ledger.beancount"]);
        run(dir.path(), &args)
    });
}

#[test]
fn python_plugin_time_budget() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"burn.py\"");
    std::fs::write(
        dir.path().join("burn.py"),
        "__plugins__ = ['burn']\ndef burn(entries, options_map):\n    while True:\n        pass\n",
    )
    .unwrap();
    both_budget_sources(dir.path(), 3, |flags| {
        let mut args = flags.to_vec();
        args.extend(["check", "ledger.beancount"]);
        run(dir.path(), &args)
    });
}

#[test]
fn wasm_importer_time_budget() {
    let Some(guests) = guests() else { return };
    let dir = tempfile::tempdir().unwrap();
    both_budget_sources(dir.path(), 1, |flags| {
        extract(dir.path(), guests, "burn", flags)
    });
}

// ---------------------------------------------------------------------------
// Limits: memory
// ---------------------------------------------------------------------------

const OUT_OF_MEMORY: &str = "ran out of the 256 MiB sandbox memory limit (rledger raises it with \
     --plugin-max-memory-mb or [plugins] max_memory_mb)";

#[test]
fn wasm_plugin_memory_cap() {
    let Some(guests) = guests() else { return };
    let dir = ledger("plugin \"conformance.wasm\" \"alloc\"");
    install_wasm_plugin(dir.path(), guests);
    run(dir.path(), &["check", "ledger.beancount"])
        .failed_cleanly()
        .has(OUT_OF_MEMORY);
}

#[test]
fn python_plugin_memory_cap() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"hog.py\"");
    // One allocation past the cap: refused by the sandbox (CPython turns
    // the refusal into a MemoryError), where an unlimited one succeeds.
    std::fs::write(
        dir.path().join("hog.py"),
        "__plugins__ = ['hog']\n\
         def hog(entries, options_map):\n    \
             held = bytearray(300 << 20)\n    \
             return entries, []\n",
    )
    .unwrap();
    run(dir.path(), &["check", "ledger.beancount"])
        .failed_cleanly()
        .has(
            "ran out of the sandbox memory limit (MemoryError; rledger raises it with \
             --plugin-max-memory-mb or [plugins] max_memory_mb)",
        );
}

#[test]
fn wasm_importer_memory_cap() {
    let Some(guests) = guests() else { return };
    let dir = tempfile::tempdir().unwrap();
    extract(dir.path(), guests, "alloc", &[])
        .failed_cleanly()
        .has(OUT_OF_MEMORY);
}

// ---------------------------------------------------------------------------
// Limits: isolation
// ---------------------------------------------------------------------------

/// A WASM plugin or importer that imports anything (here WASI's
/// `fd_read`, which a file-reading guest needs) is refused: guests get no
/// host functions at all, so no filesystem and no network.
#[test]
fn wasm_guests_cannot_import_host_functions() {
    let wat = r#"(module
        (import "wasi_snapshot_preview1" "fd_read" (func (param i32 i32 i32 i32) (result i32)))
        (memory (export "memory") 1)
        (func (export "alloc") (param i32) (result i32) i32.const 0)
        (func (export "__rustledger_abi_version") (result i32) i32.const 1)
        (func (export "process") (param i32 i32) (result i64) i64.const 0)
        (func (export "identify") (param i32 i32) (result i64) i64.const 0)
        (func (export "extract") (param i32 i32) (result i64) i64.const 0)
        (func (export "extract_enriched") (param i32 i32) (result i64) i64.const 0)
        (func (export "metadata") (result i64) i64.const 0))"#;
    let dir = ledger("plugin \"reader.wasm\"");
    std::fs::write(
        dir.path().join("reader.wasm"),
        wat::parse_str(wat).expect("WAT parses"),
    )
    .unwrap();
    run(dir.path(), &["check", "ledger.beancount"])
        .failed_cleanly()
        .has("wasi_snapshot_preview1");
    std::fs::write(dir.path().join("statement.conformance"), "x").unwrap();
    run(
        dir.path(),
        &[
            "extract",
            "--wasm-importer",
            "reader.wasm",
            "--account",
            "Assets:Bank",
            "statement.conformance",
        ],
    )
    .failed_cleanly()
    .has("forbidden import wasi_snapshot_preview1::fd_read");
}

/// A Python plugin sees exactly `/lib` (the standard library) and `/work`
/// (its inputs), both read-only, and nothing of the host: not the
/// ledger's directory, not `$HOME`, not `/etc/passwd`, not the network.
#[test]
fn python_plugin_isolation() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"probe.py\"");
    let ledger_dir = dir.path().canonicalize().unwrap();
    let home = std::env::var("HOME").unwrap_or_else(|_| "/root".to_string());
    std::fs::write(dir.path().join("secret.txt"), "host secret").unwrap();
    let probe = format!(
        r"
import os
__plugins__ = ['probe']

def _try(f):
    try:
        f()
        return 'OK'
    except Exception as e:
        return type(e).__name__

def probe(entries, options_map):
    listable = sorted(p for p in ['/', '/lib', '/work', '/tmp', '/etc', '/home',
                                  {ledger_dir:?}, {home:?}]
                      if _try(lambda: os.listdir(p)) == 'OK')
    reads = {{
        'secret': _try(lambda: open({secret:?}).read()),
        'passwd': _try(lambda: open('/etc/passwd').read()),
        'escape': _try(lambda: open('/work/../../etc/passwd').read()),
    }}
    writes = {{p: _try(lambda: open(p, 'w').write('x'))
               for p in ['/work/x', '/lib/x', '/x', '/tmp/x']}}
    net = _try(lambda: __import__('socket').create_connection(('1.1.1.1', 80), 1))
    return entries, [ValidationError(None, f'listable={{listable}}', None),
                     ValidationError(None, f'reads={{reads}}', None),
                     ValidationError(None, f'writes={{writes}}', None),
                     ValidationError(None, f'net={{net}}', None)]
",
        ledger_dir = ledger_dir.display().to_string(),
        home = home,
        secret = ledger_dir.join("secret.txt").display().to_string(),
    );
    std::fs::write(dir.path().join("probe.py"), probe).unwrap();
    let out = run(dir.path(), &["check", "ledger.beancount"]);
    out.has("listable=['/lib', '/work']").lacks("host secret");
    for line in out
        .text
        .lines()
        .filter(|l| l.contains("reads=") || l.contains("writes=") || l.contains("net="))
    {
        assert!(
            !line.contains("'OK'"),
            "the sandbox let this through: {line}"
        );
    }
    out.has("reads=").has("writes=").has("net=");
}

// ---------------------------------------------------------------------------
// Errors carry message and location
// ---------------------------------------------------------------------------

/// beancount plugins report errors as namedtuples of their own
/// (`source message entry`); rledger shows the message at the entry's
/// location, as bean-check does (`file:line: message`).
#[test]
fn python_plugin_errors_are_located() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"flag.py\"");
    std::fs::write(
        dir.path().join("flag.py"),
        "import collections\n\
         from beancount.core import data\n\
         FlagError = collections.namedtuple('FlagError', 'source message entry')\n\
         __plugins__ = ['flag']\n\
         def flag(entries, options_map):\n    \
             return entries, [FlagError(e.meta, f'flagged: {e.narration}', e)\n                     \
                              for e in data.filter_txns(entries)]\n",
    )
    .unwrap();
    run(dir.path(), &["check", "ledger.beancount"])
        .has(&format!(
            "ledger.beancount:{SNACK_LINE}:1: error[PLUGIN]: flagged: Snack"
        ))
        .lacks("FlagError(");

    // An exception names the plugin, the function and the exception.
    let dir = ledger("plugin \"boom.py\"");
    std::fs::write(
        dir.path().join("boom.py"),
        "__plugins__ = ['explode']\ndef explode(entries, options_map):\n    raise ValueError('kaboom')\n",
    )
    .unwrap();
    run(dir.path(), &["check", "ledger.beancount"])
        .has("Error applying plugin \"boom.py\" (explode): ValueError: kaboom");
}

/// Entries a Python plugin returns keep their source location, so a later
/// diagnostic (here a failing balance assertion, and the next plugin's
/// error) still points at its line, even after the plugin rebuilt them
/// (`tag_plugin` replaces each food transaction).
#[test]
fn python_plugin_output_keeps_source_locations() {
    if !python_ready() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    install_python_fixtures(dir.path());
    let text = format!(
        "plugin \"tag_plugin.py\"\nplugin \"error_plugin.py\"\n\n{BODY}\n\
         2024-01-04 balance Assets:Bank  999 USD\n"
    );
    std::fs::write(dir.path().join("ledger.beancount"), &text).unwrap();
    let balance_line = text.lines().count();
    run(dir.path(), &["check", "ledger.beancount"])
        .has(&format!(
            "ledger.beancount:{}:1: error[PLUGIN]: Transaction on 2024-01-03 has no payee",
            SNACK_LINE + 1
        ))
        .has(&format!("ledger.beancount:{balance_line}:1]"));
}

/// A plugin's metadata reaches Python, and comes back with the plugin's
/// additions, typed (#2500 review: the compat layer read a key the wire
/// never has, so plugins saw no metadata and every round trip dropped it).
#[test]
fn python_plugin_metadata_round_trip() {
    if !python_ready() {
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(
        dir.path().join("meta.py"),
        "from decimal import Decimal\n\
         __plugins__ = ['stamp']\n\
         def stamp(entries, options_map):\n    \
             out = []\n    \
             for e in entries:\n        \
                 if isinstance(e, Transaction):\n            \
                     meta = dict(e.meta)\n            \
                     meta['seen_invoice'] = e.meta.get('invoice', 'none') + '/' + e.postings[0].meta.get('pm', 'none')\n            \
                     meta['score'] = Decimal('1.50')\n            \
                     e = e._replace(meta=meta)\n        \
                 out.append(e)\n    \
             return out, []\n",
    )
    .unwrap();
    std::fs::write(
        dir.path().join("ledger.beancount"),
        "plugin \"meta.py\"\n\
         2024-01-01 open Assets:Bank USD\n\
         2024-01-01 open Expenses:Food USD\n\
         2024-01-02 * \"Shop\" \"Lunch\"\n  \
           invoice: \"INV-1\"\n  \
           Assets:Bank  -10 USD\n    \
             pm: \"p1\"\n  \
           Expenses:Food\n",
    )
    .unwrap();
    run(
        dir.path(),
        &[
            "query",
            "ledger.beancount",
            "SELECT entry_meta('invoice'), entry_meta('seen_invoice'), entry_meta('score') + 1, meta('pm')",
        ],
    )
    .has("INV-1")
    .has("INV-1/p1")
    .has("2.50")
    .has("p1");
}

/// A plugin cannot use its output to exhaust host memory: stdout is
/// capped, and a plugin past the cap is stopped with a message saying so.
#[test]
fn python_plugin_output_is_capped() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"flood.py\"");
    std::fs::write(
        dir.path().join("flood.py"),
        "import os\n\
         __plugins__ = ['flood']\n\
         def flood(entries, options_map):\n    \
             chunk = b'x' * (1 << 20)\n    \
             for _ in range(80):\n        \
                 os.write(1, chunk)\n    \
             return entries, []\n",
    )
    .unwrap();
    run(dir.path(), &["check", "ledger.beancount"])
        .failed_cleanly()
        .has("the plugin's output exceeded its");
}

// ---------------------------------------------------------------------------
// Limits: a host-set memory cap (#2500 second review)
// ---------------------------------------------------------------------------

/// Run `f` with a 1024 MiB cap set by the flag, then by the config file.
fn both_memory_sources(dir: &Path, f: impl Fn(&[&str]) -> Out) {
    f(&["--plugin-max-memory-mb", "1024"]);
    std::fs::write(dir.join("config.toml"), "[plugins]\nmax_memory_mb = 1024\n").unwrap();
    f(&[]);
    std::fs::remove_file(dir.join("config.toml")).unwrap();
}

/// A plugin that needs more than the default 256 MiB runs once the host
/// raises the cap, by flag or config, for each sandboxed kind.
#[test]
fn wasm_plugin_memory_cap_is_host_configurable() {
    let Some(guests) = guests() else { return };
    let dir = ledger("plugin \"conformance.wasm\" \"alloc\"");
    install_wasm_plugin(dir.path(), guests);
    both_memory_sources(dir.path(), |flags| {
        let mut args = flags.to_vec();
        args.extend(["check", "ledger.beancount"]);
        let out = run(dir.path(), &args);
        out.has("conformance: WASM plugin ran over 5 directives")
            .lacks("ran out");
        out
    });
}

#[test]
fn python_plugin_memory_cap_is_host_configurable() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"hog.py\"");
    std::fs::write(
        dir.path().join("hog.py"),
        "__plugins__ = ['hog']\n\
         def hog(entries, options_map):\n    \
             held = bytearray(300 << 20)\n    \
             return entries, [ValidationError(None, f'held {len(held) >> 20} MiB', None)]\n",
    )
    .unwrap();
    both_memory_sources(dir.path(), |flags| {
        let mut args = flags.to_vec();
        args.extend(["check", "ledger.beancount"]);
        let out = run(dir.path(), &args);
        out.has("held 300 MiB").lacks("MemoryError");
        out
    });
}

#[test]
fn wasm_importer_memory_cap_is_host_configurable() {
    let Some(guests) = guests() else { return };
    let dir = tempfile::tempdir().unwrap();
    both_memory_sources(dir.path(), |flags| {
        let out = extract(dir.path(), guests, "alloc", flags);
        out.has("2024-01-15 * \"conformance import\"")
            .lacks("ran out");
        out
    });
}

/// Out-of-range caps are refused, from the flag and from the config file.
#[test]
fn memory_cap_range_is_checked() {
    let dir = ledger("");
    for mb in ["0", "4097"] {
        let out = run(
            dir.path(),
            &["--plugin-max-memory-mb", mb, "check", "ledger.beancount"],
        );
        assert_eq!(out.code, Some(2), "{}", out.text);
        std::fs::write(
            dir.path().join("config.toml"),
            format!("[plugins]\nmax_memory_mb = {mb}\n"),
        )
        .unwrap();
        run(dir.path(), &["check", "ledger.beancount"])
            .has("max_memory_mb must be between 1 and 4096");
    }
}

// ---------------------------------------------------------------------------
// Limits: a hostile Python plugin (#2500 second review)
// ---------------------------------------------------------------------------

/// A temp dir with `ledger.beancount` running `name.py` = `source`.
fn python_plugin(name: &str, source: &str) -> tempfile::TempDir {
    let dir = ledger(&format!("plugin \"{name}.py\""));
    std::fs::write(dir.path().join(format!("{name}.py")), source).unwrap();
    dir
}

/// Waiting burns no fuel, so before the wall-clock deadline a plugin that
/// slept hung the host for as long as it liked.
#[test]
fn python_plugin_sleep_is_stopped_by_the_budget() {
    if !python_ready() {
        return;
    }
    let dir = python_plugin(
        "nap",
        "import time\n__plugins__ = ['nap']\ndef nap(entries, options_map):\n    \
         time.sleep(90)\n    return entries, []\n",
    );
    let start = std::time::Instant::now();
    run(
        dir.path(),
        &["--plugin-max-time-secs", "2", "check", "ledger.beancount"],
    )
    .failed_cleanly()
    .has(&budget(2))
    .has("time spent waiting or sleeping counts");
    assert!(
        start.elapsed() < std::time::Duration::from_secs(60),
        "took {:?}",
        start.elapsed()
    );
}

/// A runaway recursion is contained: it ends in the guest (out of stack
/// or memory, whichever comes first) and rledger reports it. Before, the
/// guest ran on the host thread's stack, smaller than the guest's, and
/// the host aborted with a stack overflow (SIGABRT, no diagnostics).
#[test]
fn python_plugin_deep_recursion_is_contained() {
    if !python_ready() {
        return;
    }
    let dir = python_plugin(
        "deep",
        "import sys\nsys.setrecursionlimit(10**8)\n__plugins__ = ['deep']\n\
         def down(n):\n    return down(n + 1) + 1\n\
         def deep(entries, options_map):\n    down(0)\n    return entries, []\n",
    );
    let out = run(dir.path(), &["check", "ledger.beancount"]);
    out.failed_cleanly();
    assert!(
        out.text
            .contains("the plugin recursed past the sandbox's call stack")
            || out.text.contains(OUT_OF_MEMORY),
        "{}",
        out.text
    );
}

/// Each open file is a host descriptor; a plugin that opens without
/// closing is stopped before it exhausts the host's (it reached the
/// 1024 `ulimit -n` before).
#[test]
fn python_plugin_open_files_are_capped() {
    if !python_ready() {
        return;
    }
    let dir = python_plugin(
        "hoard",
        "__plugins__ = ['hoard']\ndef hoard(entries, options_map):\n    \
         held = []\n    while True:\n        held.append(open('/work/script.py', 'rb'))\n",
    );
    run(dir.path(), &["check", "ledger.beancount"])
        .failed_cleanly()
        .has("the plugin held more than 256 files open at once");
}

/// What a plugin writes to its result stream itself is checked, not
/// trusted: output cut short, bytes that are not UTF-8, and an entry that
/// is not valid are each reported, and the load goes on (an invalid
/// entry used to abort it with `processing pipeline failed`, exit 2).
#[test]
fn python_plugin_crafted_output_is_rejected() {
    if !python_ready() {
        return;
    }
    let forge = |payload: &str| {
        format!(
            "import os\n__plugins__ = ['forge']\ndef forge(entries, options_map):\n    \
             os.write(1, {payload})\n    os._exit(0)\n"
        )
    };
    let entry =
        r#"{"date": "2024-01-01", "type": "close", "account": "Assets:Bank", "metadata": []}"#;
    let cut_short = format!("b'{{\"insert\": {entry}}}\\n'");
    run(
        python_plugin("forge", &forge(&cut_short)).path(),
        &["check", "ledger.beancount"],
    )
    .failed_cleanly()
    .has("the plugin's output ends before its result");
    run(
        python_plugin(
            "forge",
            &forge(r#"b'\xff\xfe\n{"ran": true, "errors": []}\n'"#),
        )
        .path(),
        &["check", "ledger.beancount"],
    )
    .failed_cleanly()
    .has("plugin output is not UTF-8");
    let bad_date = format!(
        "b'{{\"insert\": {}}}\\n{{\"ran\": true, \"errors\": []}}\\n'",
        entry.replace("2024-01-01", "9999-99-99")
    );
    run(python_plugin("forge", &forge(&bad_date)).path(), &["check", "ledger.beancount"])
        .failed_cleanly()
        .has("plugin returned an entry that is not valid (invalid date format: 9999-99-99); its changes were discarded")
        .lacks("processing pipeline failed");
}

/// Native `leafonly` counts an account as a parent when a child is only
/// opened, as bean-check does (`Assets:Bank:Sub` is never posted to).
#[test]
fn native_leafonly_counts_opened_children() {
    let dir = ledger("plugin \"leafonly\"");
    run(dir.path(), &["check", "ledger.beancount"])
        .has("Posting to non-leaf account 'Assets:Bank'")
        .lacks("Python");
}

// ---------------------------------------------------------------------------
// Plugin text is escaped (#2500 third review)
// ---------------------------------------------------------------------------

/// `ESC [2J` (clear screen) and an OSC title sequence, as escaped.
const ANSI_ESCAPED: &str = "\\u{1b}[2J\\u{1b}]0;pwned\\u{7}";

#[track_caller]
fn no_raw_controls(out: &Out) {
    assert!(
        !out.text.contains('\u{1b}') && !out.text.contains('\u{7}'),
        "a raw control character reached the output:\n{:?}",
        out.text
    );
}

/// What a plugin or importer says reaches the user's terminal; its control
/// characters are escaped, in every place one can put them: a Python
/// plugin's message, claimed file, exception and prints, a WASM plugin's
/// message (as a directive and through `check --plugin`), and a WASM
/// importer's warning.
#[test]
fn plugin_text_control_characters_are_escaped() {
    if python_ready() {
        let dir = python_plugin(
            "loud",
            "import sys\n__plugins__ = ['loud']\n\
             def loud(entries, options_map):\n    \
                 print('\\x1b[2J\\x1b]0;pwned\\x07 printed')\n    \
                 return entries, [ValidationError({'filename': 'f\\x1b[2J\\x1b]0;pwned\\x07', 'lineno': 3},\n                     \
                 'said \\x1b[2J\\x1b]0;pwned\\x07', None)]\n",
        );
        let out = run(dir.path(), &["check", "ledger.beancount"]);
        out.has(&format!("said {ANSI_ESCAPED}"))
            .has(&format!("f{ANSI_ESCAPED}:3"))
            .has(&format!("{ANSI_ESCAPED} printed"));
        no_raw_controls(&out);
        let dir = python_plugin(
            "raise",
            "__plugins__ = ['raise']\nraise ValueError('\\x1b[2J\\x1b]0;pwned\\x07')\n",
        );
        let out = run(dir.path(), &["check", "ledger.beancount"]);
        out.has(ANSI_ESCAPED);
        no_raw_controls(&out);
    }
    let Some(guests) = guests() else { return };
    let dir = ledger("plugin \"conformance.wasm\" \"ansi\"");
    install_wasm_plugin(dir.path(), guests);
    let out = run(dir.path(), &["check", "ledger.beancount"]);
    out.has(&format!("ran over 5 directives {ANSI_ESCAPED}"));
    no_raw_controls(&out);
    let dir = tempfile::tempdir().unwrap();
    let out = extract(dir.path(), guests, "ansi", &[]);
    out.has(&format!("conformance: WASM importer ran {ANSI_ESCAPED}"));
    no_raw_controls(&out);
}

// ---------------------------------------------------------------------------
// Lifecycle (#2500 third review)
// ---------------------------------------------------------------------------

/// Python plugins back to back, two of them stopped at the deadline
/// mid-sleep: each is reported, the next one still runs, the process ends
/// promptly (no guest thread or runtime outlives its call), and no plugin
/// leaves its temp directory behind.
#[test]
fn python_plugins_back_to_back_after_a_timeout() {
    if !python_ready() {
        return;
    }
    let dir = ledger("plugin \"nap.py\"\nplugin \"nap.py\"\nplugin \"error_plugin.py\"");
    install_python_fixtures(dir.path());
    std::fs::write(
        dir.path().join("nap.py"),
        "import time\n__plugins__ = ['nap']\ndef nap(entries, options_map):\n    \
         time.sleep(90)\n    return entries, []\n",
    )
    .unwrap();
    let tmp = tempfile::tempdir().unwrap();
    let start = std::time::Instant::now();
    let out = run_env(
        dir.path(),
        &["--plugin-max-time-secs", "2", "check", "ledger.beancount"],
        &[("TMPDIR", tmp.path())],
    );
    out.failed_cleanly()
        .has("Transaction on 2024-01-03 has no payee");
    assert_eq!(out.text.matches(&budget(2)).count(), 2, "{}", out.text);
    assert!(
        start.elapsed() < std::time::Duration::from_secs(60),
        "took {:?}",
        start.elapsed()
    );
    let left: Vec<_> = std::fs::read_dir(tmp.path()).unwrap().collect();
    assert!(left.is_empty(), "temp files left behind: {left:?}");
}

/// A Python plugin's inputs (the ledger's entries) sit in a temp
/// directory while it runs, and remain after a Ctrl-C; the directory is
/// the user's alone (it followed the umask, 0775, before).
#[cfg(unix)]
#[test]
fn python_plugin_work_dir_is_private() {
    use std::os::unix::fs::PermissionsExt;
    if !python_ready() {
        return;
    }
    let dir = python_plugin(
        "slow",
        "import time\n__plugins__ = ['slow']\ndef slow(entries, options_map):\n    \
         time.sleep(5)\n    return entries, []\n",
    );
    let tmp = tempfile::tempdir().unwrap();
    let mut child = Command::new(bin())
        .args(["check", "ledger.beancount"])
        .current_dir(dir.path())
        .env("RLEDGER_CONFIG_DIR", dir.path())
        .env("TMPDIR", tmp.path())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
    let mode = loop {
        let found = std::fs::read_dir(tmp.path())
            .unwrap()
            .filter_map(Result::ok)
            .find(|e| e.path().join("entries.jsonl").exists());
        if let Some(entry) = found {
            break entry.metadata().unwrap().permissions().mode();
        }
        assert!(
            std::time::Instant::now() < deadline,
            "the plugin's work directory never appeared"
        );
        std::thread::sleep(std::time::Duration::from_millis(50));
    };
    let _ = child.kill();
    let _ = child.wait();
    assert_eq!(mode & 0o077, 0, "work directory mode {mode:o}");
}

/// A module's own text in a load error (here its import names) is escaped
/// on every path that reports one: `check --plugin`, a `plugin`
/// directive, `extract --wasm-importer` and an importer directory scan.
#[test]
fn wasm_module_text_in_load_errors_is_escaped() {
    let wat = r#"(module
        (import "m\1b[2J\1b]0;pwned\07" "f" (func))
        (memory (export "memory") 1)
        (func (export "alloc") (param i32) (result i32) i32.const 0)
        (func (export "__rustledger_abi_version") (result i32) i32.const 1)
        (func (export "process") (param i32 i32) (result i64) i64.const 0)
        (func (export "identify") (param i32 i32) (result i64) i64.const 0)
        (func (export "extract") (param i32 i32) (result i64) i64.const 0)
        (func (export "extract_enriched") (param i32 i32) (result i64) i64.const 0)
        (func (export "metadata") (result i64) i64.const 0))"#;
    let dir = ledger("plugin \"evil.wasm\"");
    let bytes = wat::parse_str(wat).expect("WAT parses");
    std::fs::write(dir.path().join("evil.wasm"), &bytes).unwrap();
    std::fs::create_dir(dir.path().join("importers")).unwrap();
    std::fs::write(dir.path().join("importers/evil.wasm"), &bytes).unwrap();
    std::fs::write(dir.path().join("plain.beancount"), BODY).unwrap();
    std::fs::write(dir.path().join("statement.conformance"), "x").unwrap();
    let cases: [&[&str]; 4] = [
        &["check", "--plugin", "evil.wasm", "plain.beancount"],
        &["check", "ledger.beancount"],
        &[
            "extract",
            "--wasm-importer",
            "evil.wasm",
            "--account",
            "Assets:Bank",
            "statement.conformance",
        ],
        &[
            "extract",
            "--wasm-importer-dir",
            "importers",
            "--account",
            "Assets:Bank",
            "statement.conformance",
        ],
    ];
    for args in cases {
        let out = run(dir.path(), args);
        out.has("forbidden import")
            .has("m\\u{1b}[2J\\u{1b}]0;pwned\\u{7}");
        no_raw_controls(&out);
    }
}
