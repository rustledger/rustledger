//! Parity tests for the WIT/Component-Model surface (#1384).
//!
//! Instantiate the `rustledger-ffi-component` wasip2 component in a wasmtime
//! host (typed `bindgen!` bindings, no JSON-RPC) and assert its output agrees
//! with the reused `rustledger-ffi-wasi` path for the same inputs. This is what
//! actually *runs* the conversion code — the rest of the crate only compiles it.
//!
//! Requires the component to be built first:
//!   cargo build -p rustledger-ffi-component --target wasm32-wasip2
//! The tests skip (rather than fail) when the artifact is absent, so they don't
//! break a build that hasn't produced the wasip2 binary.

// `bindgen!` generates an undocumented host-bindings module; quiet its lints
// (this is a test harness, not shipped API).
#![allow(missing_docs)]
#![allow(clippy::all, clippy::pedantic, clippy::nursery)]

use anyhow::Result;
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Engine, Store};
use wasmtime_wasi::{FsPerms, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

wasmtime::component::bindgen!({
    world: "rustledger",
    path: "../rustledger-ffi-component/wit/world.wit",
});

struct Host {
    table: ResourceTable,
    wasi: WasiCtx,
}

impl WasiView for Host {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.wasi,
            table: &mut self.table,
        }
    }
}

/// A fixed "decrypted" ledger the test host returns for any ciphertext — this
/// exercises the `host.decrypt` import plumbing (#1667) without depending on a
/// real gpg binary or keyring in the test environment.
const DECRYPTED_LEDGER: &str = "\
2024-01-01 open Assets:Secret USD
2024-01-02 * \"decrypted-by-host\"
  Assets:Secret  42 USD
  Equity:Opening-Balances
";

impl rustledger::ledger::host::Host for Host {
    fn decrypt(&mut self, _ciphertext: Vec<u8>) -> Result<String, String> {
        Ok(DECRYPTED_LEDGER.to_string())
    }
}

fn component_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/wasm32-wasip2/debug/rustledger_ffi_component.wasm")
}

fn instantiate() -> Result<(Store<Host>, Rustledger)> {
    let engine = Engine::default();
    let component = Component::from_file(&engine, component_path())?;
    let mut linker = Linker::<Host>::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;
    rustledger::ledger::host::add_to_linker::<_, wasmtime::component::HasSelf<Host>>(
        &mut linker,
        |h| h,
    )?;
    let mut store = Store::new(
        &engine,
        Host {
            table: ResourceTable::new(),
            wasi: WasiCtxBuilder::new().build(),
        },
    );
    let inst = Rustledger::instantiate(&mut store, &component, &linker)?;
    Ok((store, inst))
}

/// Like [`instantiate`], but grants the guest read access to `host_dir`,
/// mounted at `/work`, so `load-file` can read files through WASI.
fn instantiate_in(host_dir: &std::path::Path) -> Result<(Store<Host>, Rustledger)> {
    let engine = Engine::default();
    let component = Component::from_file(&engine, component_path())?;
    let mut linker = Linker::<Host>::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;
    rustledger::ledger::host::add_to_linker::<_, wasmtime::component::HasSelf<Host>>(
        &mut linker,
        |h| h,
    )?;
    let wasi = WasiCtxBuilder::new()
        .preopened_dir(host_dir, "/work", FsPerms::ReadOnly)?
        .build();
    let mut store = Store::new(
        &engine,
        Host {
            table: ResourceTable::new(),
            wasi,
        },
    );
    let inst = Rustledger::instantiate(&mut store, &component, &linker)?;
    Ok((store, inst))
}

const LEDGER: &str = "\
2024-01-01 open Assets:Cash USD
2024-01-01 open Expenses:Food USD
2024-01-02 * \"Coffee\"
  Expenses:Food  5 USD
  Assets:Cash
";

/// The `major.minor` of the `package rustledger:ledger@X.Y.Z;` line in the WIT
/// contract — the single source of truth the runtime `version()` (i.e. the
/// `API_VERSION` const) must mirror.
fn wit_package_api_version() -> String {
    const WIT: &str = include_str!("../../rustledger-ffi-component/wit/world.wit");
    let full = WIT
        .lines()
        .find_map(|l| l.trim().strip_prefix("package rustledger:ledger@"))
        .and_then(|s| s.split(';').next())
        .expect("world.wit must declare `package rustledger:ledger@X.Y.Z;`")
        .trim();
    let mut parts = full.split('.');
    let major = parts.next().expect("major");
    let minor = parts.next().expect("minor");
    format!("{major}.{minor}")
}

/// The runtime `version()` (the `API_VERSION` const) must stay in lockstep with
/// the WIT package version (#1395). If a contract change bumps
/// `package rustledger:ledger@X.Y.Z;` but not `API_VERSION` (or vice-versa),
/// embedders negotiating on `version()` would see a version that doesn't match
/// the actual contract. The CI `wit-version-gate` ensures the *package* version
/// is bumped on a WIT change; this test ensures the *runtime* version tracks it.
#[test]
fn version_matches_wit_package() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let version = inst.rustledger_ledger_ledger().call_version(&mut store)?;
    assert_eq!(
        version,
        wit_package_api_version(),
        "runtime version() / API_VERSION must equal the world.wit package \
         major.minor — bump them together",
    );
    Ok(())
}

#[test]
fn load_entry_count_matches_jsonrpc() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let result = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, LEDGER, "<stdin>", false)?;
    let expected = rustledger_ffi_wasi::helpers::load_source(LEDGER)
        .directives
        .len();
    assert_eq!(
        result.entries.len(),
        expected,
        "component load entry count must match load_source",
    );
    assert!(expected >= 3);
    Ok(())
}

#[test]
fn query_row_count_matches_executor() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let q = "SELECT account, position";
    let result = inst
        .rustledger_ledger_ledger()
        .call_query(&mut store, LEDGER, q)?;
    assert!(
        result.errors.is_empty(),
        "query errored: {:?}",
        result.errors
    );
    assert!(
        !result.rows.is_empty(),
        "expected query rows for a non-empty ledger",
    );
    Ok(())
}

const LEDGER_WITH_HISTORY: &str = "\
2023-01-01 open Assets:Cash USD
2023-01-01 open Equity:Opening-Balances USD
2023-06-01 * \"old deposit\"
  Assets:Cash  100 USD
  Equity:Opening-Balances  -100 USD
2024-03-01 * \"in range\"
  Assets:Cash  -5 USD
  Expenses:Food  5 USD
";

#[test]
fn clamp_runs_and_summarizes_pre_range() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let loaded = inst.rustledger_ledger_ledger().call_load(
        &mut store,
        LEDGER_WITH_HISTORY,
        "<stdin>",
        false,
    )?;
    let clamped = inst.rustledger_ledger_builder().call_clamp(
        &mut store,
        &loaded.entries,
        "2024-01-01",
        "2024-12-31",
    )?;
    // Produces output, and no surviving directive predates the clamp window.
    assert!(!clamped.is_empty(), "clamp returned nothing");
    Ok(())
}

// Regression tests for the parity bugs the deep review found (the conversion
// layer was diverging from the JSON-RPC handlers on these cases).

#[test]
fn query_expands_pads() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let src = "\
2024-01-01 open Assets:Cash USD
2024-01-01 open Equity:Opening USD
2024-01-01 pad Assets:Cash Equity:Opening
2024-06-01 balance Assets:Cash 500 USD
";
    let r = inst.rustledger_ledger_ledger().call_query(
        &mut store,
        src,
        "SELECT account, balance WHERE account = \"Assets:Cash\"",
    )?;
    assert!(r.errors.is_empty(), "query errored: {:?}", r.errors);
    assert!(!r.rows.is_empty(), "expected a row for Assets:Cash");
    // With pad expansion the balance is 500; without it the pad contributes nothing.
    let dump = format!("{:?}", r.rows);
    assert!(
        dump.contains("500"),
        "expected padded balance 500, got: {dump}"
    );
    Ok(())
}

#[test]
fn query_short_circuits_on_parse_error() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    // `oepn` is a typo -> parse error.
    let r = inst.rustledger_ledger_ledger().call_query(
        &mut store,
        "2024-01-01 oepn Assets:Cash\n",
        "SELECT account",
    )?;
    assert!(
        !r.errors.is_empty(),
        "parse error must surface, not be swallowed"
    );
    assert!(r.rows.is_empty(), "no rows on parse error");
    Ok(())
}

#[test]
fn filter_keeps_pre_begin_open_and_drops_commodity() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    use rustledger::ledger::types::Directive;
    let (mut store, inst) = instantiate()?;
    let src = "\
2020-01-01 open Assets:Cash USD
2024-03-01 commodity USD
2024-06-01 * \"x\"
  Assets:Cash  1 USD
  Expenses:Y  -1 USD
";
    let loaded = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, src, "<stdin>", false)?;
    let filtered = inst.rustledger_ledger_builder().call_filter(
        &mut store,
        &loaded.entries,
        "2024-01-01",
        "2024-12-31",
    )?;
    assert!(
        filtered.iter().any(|d| matches!(d, Directive::Open(_))),
        "pre-begin open must be kept (open < end)",
    );
    assert!(
        filtered
            .iter()
            .all(|d| !matches!(d, Directive::Commodity(_))),
        "commodity must be dropped",
    );
    Ok(())
}

#[test]
fn custom_directive_values_keep_their_type_tag() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    use rustledger::ledger::types::Directive;
    let (mut store, inst) = instantiate()?;
    // A `custom` directive whose args have distinct types: an account and a
    // string. `meta-value` alone would flatten both to `text`; `typed-value`
    // must preserve `value-type` ("account" vs "string").
    let src = "2024-01-01 custom \"budget\" Assets:Cash \"monthly\"\n";
    let loaded = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, src, "<stdin>", false)?;
    let custom = loaded
        .entries
        .iter()
        .find_map(|d| match d {
            Directive::Custom(c) => Some(c),
            _ => None,
        })
        .expect("expected a custom directive");
    let types: Vec<&str> = custom
        .values
        .iter()
        .map(|tv| tv.value_type.as_str())
        .collect();
    assert!(
        types.contains(&"account"),
        "account arg must keep value-type \"account\", got {types:?}",
    );
    assert!(
        types.contains(&"string"),
        "quoted arg must keep value-type \"string\", got {types:?}",
    );
    Ok(())
}

// End-to-end `load-file` tests (#1402). These exercise the file path through
// WASI: the host preopens a temp dir at `/work`, the guest reads `.bean` files
// from it. This is the only coverage of the `load-file` export and its
// `allow-unrestricted-includes` / `plugins` parameters.

#[test]
fn load_file_reads_and_resolves_includes() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("sub.bean"),
        "2024-01-01 open Assets:Cash USD\n",
    )?;
    std::fs::write(
        dir.path().join("main.bean"),
        "include \"sub.bean\"\n2024-01-02 open Expenses:Food USD\n",
    )?;
    let (mut store, inst) = instantiate_in(dir.path())?;
    let r = inst.rustledger_ledger_ledger().call_load_file(
        &mut store,
        "/work/main.bean",
        true,
        &[],
        false,
    )?;
    assert!(r.errors.is_empty(), "load_file errored: {:?}", r.errors);
    // Opens from both the entry file and the included file.
    assert!(
        r.entries.len() >= 2,
        "expected entries from main + included file, got {}",
        r.entries.len(),
    );
    Ok(())
}

#[test]
fn load_file_path_security_confines_cross_tree_includes() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    let dir = tempfile::tempdir()?;
    std::fs::create_dir(dir.path().join("entry"))?;
    std::fs::create_dir(dir.path().join("sibling"))?;
    std::fs::write(
        dir.path().join("sibling/data.bean"),
        "2024-01-01 open Assets:Cash USD\n",
    )?;
    std::fs::write(
        dir.path().join("entry/main.bean"),
        "include \"../sibling/data.bean\"\n2024-01-02 open Expenses:Food USD\n",
    )?;
    let (mut store, inst) = instantiate_in(dir.path())?;
    // Confined (allow-unrestricted-includes = false): the `../sibling` include
    // escapes the entry file's directory tree and must be rejected.
    let confined = inst.rustledger_ledger_ledger().call_load_file(
        &mut store,
        "/work/entry/main.bean",
        false,
        &[],
        false,
    )?;
    // Assert specifically on the path-traversal rejection, not just any error,
    // so an incidental I/O or parse failure can't make this pass for the wrong
    // reason. (The unrestricted branch below resolving cleanly already proves
    // the file is readable and well-formed.)
    assert!(
        confined
            .errors
            .iter()
            .any(|e| e.message.contains("path traversal not allowed")),
        "confined load must reject the cross-tree include with a path-traversal error, got: {:?}",
        confined.errors,
    );
    // Unrestricted (true): the same include resolves cleanly.
    let open = inst.rustledger_ledger_ledger().call_load_file(
        &mut store,
        "/work/entry/main.bean",
        true,
        &[],
        false,
    )?;
    assert!(
        open.errors.is_empty(),
        "cross-tree include should resolve when unrestricted: {:?}",
        open.errors,
    );
    Ok(())
}

#[test]
fn load_file_runs_requested_plugin() -> Result<()> {
    if !component_path().exists() {
        return Ok(());
    }
    use rustledger::ledger::types::Directive;
    let dir = tempfile::tempdir()?;
    // A lot purchased at cost; `implicit_prices` synthesizes a Price directive.
    std::fs::write(
        dir.path().join("main.bean"),
        "\
2024-01-01 open Assets:Cash USD
2024-01-01 open Assets:Stock STOCK
2024-01-02 * \"buy\"
  Assets:Stock  10 STOCK {5 USD}
  Assets:Cash  -50 USD
",
    )?;
    let (mut store, inst) = instantiate_in(dir.path())?;
    let without = inst.rustledger_ledger_ledger().call_load_file(
        &mut store,
        "/work/main.bean",
        true,
        &[],
        false,
    )?;
    let with = inst.rustledger_ledger_ledger().call_load_file(
        &mut store,
        "/work/main.bean",
        true,
        &["implicit_prices".to_string()],
        false,
    )?;
    let count_prices = |entries: &[Directive]| {
        entries
            .iter()
            .filter(|d| matches!(d, Directive::Price(_)))
            .count()
    };
    assert!(
        count_prices(&with.entries) > count_prices(&without.entries),
        "implicit_prices should synthesize a Price directive: without={} with={}",
        count_prices(&without.entries),
        count_prices(&with.entries),
    );
    Ok(())
}

/// The component must run the pre-booking SYNTH pass (`auto_accounts`) declared
/// in a ledger, generating `Open` directives that surface with the generated
/// marker (`meta.lineno == 0`) — through BOTH `load` (string) and `load-file`.
///
/// Regression guard for the duplicated-pipeline bug where the reused `ffi-wasi`
/// helpers hand-rolled a partial loader that skipped synth entirely.
const AUTO_ACCOUNTS_LEDGER: &str = "\
option \"operating_currency\" \"USD\"
plugin \"auto_accounts\"

2024-01-15 * \"Paycheck\"
  Assets:Bank:Checking                    5000 USD
  Income:Salary                          -5000 USD

2024-01-20 * \"Groceries\"
  Expenses:Food                            50 USD
  Assets:Bank:Checking                    -50 USD
";

const SYNTH_ACCOUNTS: [&str; 3] = ["Assets:Bank:Checking", "Income:Salary", "Expenses:Food"];

fn assert_generated_opens(entries: &[rustledger::ledger::types::Directive], surface: &str) {
    use rustledger::ledger::types::Directive;
    let opens: Vec<(String, u32)> = entries
        .iter()
        .filter_map(|d| match d {
            Directive::Open(o) => Some((o.account.clone(), o.meta.lineno)),
            _ => None,
        })
        .collect();
    for acct in SYNTH_ACCOUNTS {
        assert!(
            opens.iter().any(|(a, line)| a == acct && *line == 0),
            "{surface}: auto_accounts should synthesize a generated Open (lineno 0) for {acct}; got: {opens:?}",
        );
    }
}

#[test]
fn load_runs_auto_accounts_synth() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let loaded = inst.rustledger_ledger_ledger().call_load(
        &mut store,
        AUTO_ACCOUNTS_LEDGER,
        "<stdin>",
        false,
    )?;
    assert_generated_opens(&loaded.entries, "component load");
    Ok(())
}

#[test]
fn load_file_runs_auto_accounts_synth() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let dir = tempfile::tempdir()?;
    std::fs::write(dir.path().join("main.bean"), AUTO_ACCOUNTS_LEDGER)?;
    let (mut store, inst) = instantiate_in(dir.path())?;
    let loaded = inst.rustledger_ledger_ledger().call_load_file(
        &mut store,
        "/work/main.bean",
        true,
        &[],
        false,
    )?;
    assert_generated_opens(&loaded.entries, "component load_file");
    Ok(())
}

const LEDGER_WITH_COST: &str = "\
2023-01-01 open Assets:Cash USD
2023-01-01 open Expenses:Food USD
2023-06-15 * \"old\"
  Expenses:Food  5 USD
  Assets:Cash
2024-02-10 * \"Coffee\"
  Expenses:Food  7 USD {2 USD}
  Assets:Cash  -14 USD
";

/// `from-entries-with-options` (WIT 3.7.0, #1766): a session rebuilt
/// from another session's `info()` carries the ledger's OPTIONS across
/// the component boundary, so BQL `POSSIGN` classifies renamed account
/// roots — where the options-less `from-entries` documents the default
/// classifier. The sign flip is the exact observable the L5 note
/// recorded as broken.
#[test]
fn session_from_entries_with_options_carries_renamed_roots() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let ledger = inst.rustledger_ledger_ledger();
    let session = ledger.session();

    const RENAMED: &str = concat!(
        "option \"name_income\" \"Einnahmen\"\n",
        "2024-01-01 open Einnahmen:Salary\n",
        "2024-01-01 open Assets:Bank\n",
        "\n",
        "2024-01-02 * \"pay\"\n",
        "  Assets:Bank  100.00 USD\n",
        "  Einnahmen:Salary\n",
    );
    let loaded = session.call_constructor(&mut store, RENAMED)?;
    let info = session.call_info(&mut store, loaded)?;
    assert!(info.errors.is_empty(), "load errored: {:?}", info.errors);
    assert_eq!(info.options.name_income, "Einnahmen");

    let q = "SELECT possign(100, 'Einnahmen:Salary')";

    // Exact-variant matching, not a debug-substring proxy (Copilot
    // review: `contains("-100")` also matches "-1000").
    fn first_number(r: &exports::rustledger::ledger::ledger::QueryResult) -> &str {
        match r
            .rows
            .first()
            .and_then(|row| row.first())
            .expect("query returns at least one row")
        {
            rustledger::ledger::types::QueryValue::Number(n) => n.as_str(),
            other => panic!("POSSIGN must return query-value::number, got {other:?}"),
        }
    }

    let with_options =
        session.call_from_entries_with_options(&mut store, &info.entries, &info.options)?;
    let r = session.call_query(&mut store, with_options, q)?;
    assert!(r.errors.is_empty(), "query errored: {:?}", r.errors);
    assert_eq!(
        first_number(&r),
        "-100",
        "held options must POSSIGN-negate the renamed income root"
    );

    let without_options = session.call_from_entries(&mut store, &info.entries)?;
    let r = session.call_query(&mut store, without_options, q)?;
    assert!(r.errors.is_empty(), "query errored: {:?}", r.errors);
    assert_eq!(
        first_number(&r),
        "100",
        "options-less entries default the classifier (documented, #1766)"
    );
    Ok(())
}

/// `session.format` (WIT 3.8.0, #1766): render the held entries honoring
/// the ledger's display precision, over the real component boundary. The
/// distinguishing observable: an option precision WIDER than every written
/// amount (3dp vs 2dp) — inference alone can never produce the padded
/// third decimal, so it proves `display-precision` crossed the boundary
/// and reached the renderer. Also pins the `info()` ->
/// `from-entries-with-options` round trip (pads WITH the options, falls
/// back to entry-inferred 2dp without).
#[test]
fn session_format_honors_display_precision() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let ledger = inst.rustledger_ledger_ledger();
    let session = ledger.session();

    const PRECISION_LEDGER: &str = concat!(
        "option \"display_precision\" \"USD:0.001\"\n",
        "2024-01-01 open Assets:Bank\n",
        "2024-01-15 balance Assets:Bank  100.50 USD\n",
    );
    let loaded = session.call_constructor(&mut store, PRECISION_LEDGER)?;
    let info = session.call_info(&mut store, loaded)?;
    assert!(info.errors.is_empty(), "load errored: {:?}", info.errors);
    assert!(
        info.options
            .display_precision
            .contains(&("USD".to_string(), 3)),
        "options must carry the resolved USD 3dp, got {:?}",
        info.options.display_precision
    );

    let text = session
        .call_format(&mut store, loaded)?
        .map_err(|e| anyhow::anyhow!("format failed: {e}"))?;
    assert!(
        text.contains("2024-01-15 balance Assets:Bank 100.500 USD\n"),
        "option 3dp must pad the written 2dp amount, got:\n{text}"
    );

    let with_options =
        session.call_from_entries_with_options(&mut store, &info.entries, &info.options)?;
    let text = session
        .call_format(&mut store, with_options)?
        .map_err(|e| anyhow::anyhow!("format failed: {e}"))?;
    assert!(
        text.contains("2024-01-15 balance Assets:Bank 100.500 USD\n"),
        "held options must pad to 3dp after the round trip, got:\n{text}"
    );

    let without_options = session.call_from_entries(&mut store, &info.entries)?;
    let text = session
        .call_format(&mut store, without_options)?
        .map_err(|e| anyhow::anyhow!("format failed: {e}"))?;
    assert!(
        text.contains("2024-01-15 balance Assets:Bank 100.50 USD\n"),
        "options-less entries keep the entry-inferred 2dp, got:\n{text}"
    );
    Ok(())
}

/// `session.returns` (WIT 3.9.0, #1847): the component's returns over the held
/// ledger must equal the NATIVE `rustledger_query::scope_returns` over the same
/// interpolated, pad-expanded stream — the SAME composition the CLI's `report returns`
/// calls, so this pins the wasm surface against the CLI's returns path, not a
/// private re-implementation. Drift guard across the wasm boundary: the decimal
/// fields (rust_decimal, pure integer arithmetic) must match byte-for-byte; the
/// two `f64` rates are compared within a tolerance, since wasm and native float
/// can differ by an ULP in the XIRR/TWR iteration.
#[test]
fn session_returns_matches_native_engine() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    const LEDGER: &str = "\
option \"operating_currency\" \"USD\"
2020-01-01 open Assets:Invest:Broker
2020-01-01 open Assets:Cash
2020-01-01 open Income:Dividends
2020-01-01 * \"Buy 10 ACME\"
  Assets:Invest:Broker  10 ACME {100 USD}
  Assets:Cash
2020-07-01 * \"Dividend\"
  Assets:Cash  20 USD
  Income:Dividends
2021-01-01 price ACME  120 USD
";
    let investments = vec!["Assets:Invest".to_string()];
    let income = vec!["Income".to_string()];

    // Component side: hold the ledger and ask for returns over the boundary.
    let (mut store, inst) = instantiate()?;
    let session = inst.rustledger_ledger_ledger().session();
    let handle = session.call_constructor(&mut store, LEDGER)?;
    let via = session
        .call_returns(
            &mut store,
            handle,
            &investments,
            &income,
            "USD",
            "2021-01-01",
        )?
        .map_err(|e| anyhow::anyhow!("returns failed: {e}"))?;
    handle.resource_drop(&mut store)?;

    // Native reference: the shared helper both the CLI and the component call.
    let native = rustledger_ffi_wasi::helpers::load_source(LEDGER);
    assert!(
        native.errors.is_empty(),
        "fixture must load without errors ({} found)",
        native.errors.len()
    );
    let padded = rustledger_booking::merge_with_padding(&native.directives);
    let scope = rustledger_returns::Scope::new(investments.clone(), income.clone());
    let end = "2021-01-01".parse().expect("date");
    let direct = rustledger_query::scope_returns(&padded, &scope, "USD", end)
        .expect("native engine computes");

    // Decimal fields: exact (rust_decimal is deterministic across targets).
    assert_eq!(via.cash_flows, u32::try_from(direct.cash_flows).unwrap());
    assert_eq!(via.invested, direct.invested.to_string());
    assert_eq!(via.distributions, direct.distributions.to_string());
    assert_eq!(via.current_value, direct.current_value.to_string());

    // Rates: within tolerance (wasm vs native float).
    let approx = |a: Option<f64>, b: Option<f64>| match (a, b) {
        (Some(x), Some(y)) => (x - y).abs() < 1e-9,
        (None, None) => true,
        _ => false,
    };
    assert!(
        approx(via.money_weighted, direct.money_weighted),
        "MWR drift: component {:?} vs native {:?}",
        via.money_weighted,
        direct.money_weighted
    );
    assert!(
        approx(via.time_weighted, direct.time_weighted),
        "TWR drift: component {:?} vs native {:?}",
        via.time_weighted,
        direct.time_weighted
    );
    Ok(())
}

/// The stateful `resource session` (#173): construct once, then info/query/
/// clamp run against the held ledger. Crucially `clamp` operates on the held
/// core directives, so cost basis survives with no WIT->core->WIT round-trip.
#[test]
fn session_clamp_preserves_cost_basis() -> Result<()> {
    use rustledger::ledger::types::{CostNumber, Directive};

    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let ledger = inst.rustledger_ledger_ledger();
    let session = ledger.session();

    let handle = session.call_constructor(&mut store, LEDGER_WITH_COST)?;

    // `info` materializes the load result once; entry count matches the loader.
    let info = session.call_info(&mut store, handle)?;
    let expected = rustledger_ffi_wasi::helpers::load_source(LEDGER_WITH_COST)
        .directives
        .len();
    assert_eq!(info.entries.len(), expected);
    assert!(info.errors.is_empty(), "load errored: {:?}", info.errors);

    // Query runs against the held ledger.
    let q = session.call_query(&mut store, handle, "SELECT account, position")?;
    assert!(q.errors.is_empty(), "query errored: {:?}", q.errors);
    assert!(!q.rows.is_empty());

    // Clamp on the held core directives preserves the per-unit cost basis.
    let clamped = session.call_clamp(&mut store, handle, "2024-01-01", "2024-12-31")?;
    let coffee = clamped
        .iter()
        .find_map(|d| match d {
            Directive::Transaction(t) if t.narration.as_deref() == Some("Coffee") => Some(t),
            _ => None,
        })
        .expect("Coffee transaction survived the clamp window");
    let cost = coffee.postings[0]
        .cost
        .as_ref()
        .expect("Coffee posting kept its cost");
    assert!(
        matches!(&cost.number, Some(CostNumber::PerUnit(v)) if v == "2"),
        "cost basis preserved through clamp: {:?}",
        cost.number,
    );

    handle.resource_drop(&mut store)?;
    Ok(())
}

/// #1656: a held-at-cost lot summarized into the clamp opening balance must keep
/// its cost on the `Equity:Opening-Balances` contra, so the opening transaction
/// balances by weight. The component's `clamp` is what rustfava uses for time
/// filtering; a bare-units contra breaks any at-cost view of the clamped ledger.
#[test]
fn clamp_opening_balance_contra_keeps_cost() -> Result<()> {
    use rustledger::ledger::types::Directive;
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let comp = inst.rustledger_ledger_ledger();
    let session = comp.session();
    let src = "\
2000-01-01 open Assets:MC
2000-01-01 open Equity:Open
2000-01-02 * \"seed\"
  Assets:MC   100 USD
  Equity:Open  -100 USD
2000-01-03 * \"buy\"
  Assets:MC    1 XYZ {50 USD}
  Assets:MC  -50 USD
";
    let handle = session.call_constructor(&mut store, src)?;
    // Clamp to a window AFTER all entries: everything becomes opening balance.
    let clamped = session.call_clamp(&mut store, handle, "2014-01-01", "2015-01-01")?;
    let opening = clamped
        .iter()
        .find_map(|d| match d {
            Directive::Transaction(t) if t.narration.as_deref() == Some("Opening balance") => {
                Some(t)
            }
            _ => None,
        })
        .expect("an Opening balance transaction is synthesized");
    let xyz_contra = opening
        .postings
        .iter()
        .find(|p| {
            p.account == "Equity:Opening-Balances"
                && p.units.as_ref().is_some_and(|u| u.currency == "XYZ")
        })
        .expect("an Equity:Opening-Balances contra for the XYZ lot");
    assert!(
        xyz_contra.cost.is_some(),
        "held-at-cost contra must keep its cost through the component clamp (#1656)",
    );
    handle.resource_drop(&mut store)?;
    Ok(())
}

/// `builder.query-entries` (rustfava#173): query an already-loaded directive
/// set directly, matching the source-based `query` — the typed alternative to
/// re-rendering entries to source.
#[test]
fn query_entries_matches_source_query() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let q = "SELECT account, position";
    let loaded = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, LEDGER, "<stdin>", false)?;
    let via_entries =
        inst.rustledger_ledger_builder()
            .call_query_entries(&mut store, &loaded.entries, q)?;
    let via_source = inst
        .rustledger_ledger_ledger()
        .call_query(&mut store, LEDGER, q)?;
    assert!(
        via_entries.errors.is_empty(),
        "query-entries errored: {:?}",
        via_entries.errors
    );
    assert!(!via_entries.rows.is_empty());
    assert_eq!(
        via_entries.rows.len(),
        via_source.rows.len(),
        "query-entries must match source query row count",
    );
    Ok(())
}

/// `@@` (total price) must surface through the component as a **per-unit** price,
/// exactly as `rledger check` reports it. The `@@`→`@` conversion lives in the
/// loader's shared `finalize` phase, so the FFI surface and the CLI cannot
/// disagree.
///
/// Regression guard for the v0.17.0 bug: the FFI path exposed the raw `@@` total
/// (`7 USD @@ 10 EUR` → price `10`) instead of the per-unit price (`10/7 ≈
/// 1.4286`), because the normalization had lived only in the CLI `check` path
/// and was lost when the FFI surface moved onto the shared pipeline (#1462).
#[test]
fn total_price_at_at_normalized_to_per_unit() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    use rustledger::ledger::types::Directive;
    let (mut store, inst) = instantiate()?;
    let ledger = "\
2024-01-01 open Assets:Cash USD
2024-01-01 open Assets:Other EUR
2024-01-02 * \"total price\"
  Assets:Cash   7 USD @@ 10 EUR
  Assets:Other  -10 EUR
";
    let loaded = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, ledger, "<stdin>", false)?;
    let (number, currency) = loaded
        .entries
        .iter()
        .find_map(|d| match d {
            Directive::Transaction(t) => t.postings.iter().find_map(|p| {
                p.price
                    .as_ref()
                    .map(|a| (a.number.clone(), a.currency.clone()))
            }),
            _ => None,
        })
        .expect("the `@@` posting should carry a price");
    assert_eq!(currency, "EUR");
    // 10 EUR / 7 USD = 1.4285714… per unit — NOT the raw total `10`.
    assert!(
        number.starts_with("1.42857"),
        "`@@` total must be normalized to per-unit, got `{number}` {currency}",
    );
    Ok(())
}

/// #1663: `load` (not only `validate`) must report balance-assertion failures,
/// so an embedder that loads via `load` (rustfava) sees a failing `balance`
/// instead of a silent green. Load-vs-validate parity for the balance check.
#[test]
fn load_reports_balance_assertion_failure() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    // Real balance of Assets:Cash is -5 USD, but the ledger asserts 999 USD.
    let src = "\
2024-01-01 open Assets:Cash USD
2024-01-01 open Expenses:X USD
2024-01-02 * \"t\"
  Expenses:X   5 USD
  Assets:Cash
2024-01-03 balance Assets:Cash   999 USD
";
    let loaded = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, src, "<stdin>", false)?;
    let has_balance_err = loaded
        .errors
        .iter()
        .any(|e| e.message.contains("Balance failed") && e.message.contains("Assets:Cash"));
    assert!(
        has_balance_err,
        "`load` must surface the failing balance assertion (#1663); got errors: {:?}",
        loaded
            .errors
            .iter()
            .map(|e| e.message.clone())
            .collect::<Vec<_>>()
    );

    // #1663 Part 2: the balance directive carries the computed diff (WIT 3.1.0),
    // so UIs render pass/fail without re-deriving. computed(-5) − asserted(999).
    let bal_diff = loaded
        .entries
        .iter()
        .find_map(|d| match d {
            rustledger::ledger::types::Directive::Balance(b) => b.diff.clone(),
            _ => None,
        })
        .expect("the balance directive should carry a diff (#1663 Part 2)");
    assert_eq!(bal_diff.currency, "USD");
    assert!(
        bal_diff.number.starts_with("-1004"),
        "diff should be computed − asserted = -1004, got `{}`",
        bal_diff.number
    );
    Ok(())
}

/// #1668: an oversell reports the "Not enough units" error exactly ONCE via
/// `load`. Booking (run inside `load_source`) already reports it with
/// transaction context; the validation session's context-free reduce-check
/// (a standalone-validation safety net) must not duplicate it.
#[test]
fn load_oversell_reports_single_error() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let src = "\
2020-01-01 open Assets:S
2020-01-01 open Assets:Cash
2020-02-01 * \"buy\"
  Assets:S   5 X {10 USD}
  Assets:Cash
2020-03-01 * \"oversell\"
  Assets:S   -10 X {10 USD}
  Assets:Cash   100 USD
";
    let loaded = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, src, "<stdin>", false)?;
    let n = loaded
        .errors
        .iter()
        .filter(|e| e.message.contains("Not enough units"))
        .count();
    assert_eq!(
        n,
        1,
        "oversell must report 'Not enough units' exactly once (#1668); got {n}: {:?}",
        loaded
            .errors
            .iter()
            .map(|e| e.message.clone())
            .collect::<Vec<_>>()
    );
    Ok(())
}

/// #1667: an encrypted (`.gpg`) ledger loads through the component by delegating
/// decryption to the `host.decrypt` import — the WASI sandbox can neither spawn
/// `gpg` nor reach the keyring. The test host returns `DECRYPTED_LEDGER` for any
/// ciphertext; we assert that plaintext is what gets parsed.
#[test]
fn load_file_decrypts_via_host_import() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let dir = tempfile::tempdir()?;
    // Content is irrelevant — the `.gpg` extension marks the file as encrypted,
    // and the test host returns a fixed plaintext for any bytes.
    std::fs::write(
        dir.path().join("ledger.beancount.gpg"),
        b"not-really-gpg-ciphertext",
    )?;
    let (mut store, inst) = instantiate_in(dir.path())?;
    let loaded = inst.rustledger_ledger_ledger().call_load_file(
        &mut store,
        "/work/ledger.beancount.gpg",
        false,
        &[],
        false,
    )?;
    // The host-decrypted ledger opens Assets:Secret — proof the plaintext from
    // `host.decrypt` is what got parsed (versus the old `failed to decrypt`).
    let has_secret = loaded.entries.iter().any(|d| {
        matches!(
            d,
            rustledger::ledger::types::Directive::Open(o) if o.account == "Assets:Secret"
        )
    });
    assert!(
        has_secret,
        "encrypted ledger must load via host.decrypt (#1667); {} entries, errors: {:?}",
        loaded.entries.len(),
        loaded
            .errors
            .iter()
            .map(|e| e.message.clone())
            .collect::<Vec<_>>()
    );
    Ok(())
}

/// The `importer` interface (3.5.0) over the real component: identify a CSV,
/// infer its mapping, extract with the inferred config, and agree with the
/// native `rustledger-importer` engine on the result.
#[test]
fn importer_extract_matches_native_engine() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    const CSV: &str =
        "Date,Description,Amount\n2026-07-01,Coffee Shop,-4.50\n2026-07-02,Salary,2500.00\n";
    let (mut store, inst) = instantiate()?;
    let importer = inst.rustledger_ledger_importer();

    let names = importer.call_identify(&mut store, "bank.csv", CSV.as_bytes())?;
    assert_eq!(names, vec!["CSV".to_string()]);

    let config = importer
        .call_infer(&mut store, "bank.csv", CSV.as_bytes())?
        .expect("CSV is inferable");
    let config = format!("{config}account = \"Assets:Bank\"\ncurrency = \"USD\"\n");
    let result = importer
        .call_extract(&mut store, "bank.csv", CSV.as_bytes(), &config)?
        .expect("extraction succeeds");

    // Native engine on the same content + config — the drift guard.
    let entry = rustledger_importer::toml_entry::ImporterEntry::from_toml_str(&config)?;
    let native_cfg = rustledger_importer::toml_entry::build_config_from_entry(&entry)?;
    let native = rustledger_importer::csv_importer::CsvImporter.extract_string(CSV, &native_cfg)?;

    // Compare the exact observables (date, narration, postings), not just
    // counts — a count-only guard is decoration per the drift-guard rule.
    fn wit_shape(
        d: &rustledger::ledger::types::Directive,
    ) -> (String, String, Vec<(String, String)>) {
        let rustledger::ledger::types::Directive::Transaction(t) = d else {
            panic!("expected transaction, got {d:?}");
        };
        (
            t.date.clone(),
            t.narration.clone().unwrap_or_default(),
            t.postings
                .iter()
                .map(|p| {
                    let units = p
                        .units
                        .as_ref()
                        .map(|u| format!("{} {}", u.number, u.currency))
                        .unwrap_or_default();
                    (p.account.clone(), units)
                })
                .collect(),
        )
    }
    fn native_shape(d: &rustledger_core::Directive) -> (String, String, Vec<(String, String)>) {
        let rustledger_core::Directive::Transaction(t) = d else {
            panic!("expected transaction, got {d:?}");
        };
        (
            t.date.to_string(),
            t.narration.to_string(),
            t.postings
                .iter()
                .map(|p| {
                    let units = p
                        .amount()
                        .map(|a| format!("{} {}", a.number, a.currency))
                        .unwrap_or_default();
                    (p.account.to_string(), units)
                })
                .collect(),
        )
    }
    let component_shapes: Vec<_> = result.entries.iter().map(wit_shape).collect();
    let native_shapes: Vec<_> = native.directives.iter().map(native_shape).collect();
    assert_eq!(component_shapes, native_shapes);
    assert_eq!(component_shapes.len(), 2);
    let warning_messages: Vec<&str> = result.warnings.iter().map(|w| w.message.as_str()).collect();
    let native_warnings: Vec<&str> = native.warnings.iter().map(String::as_str).collect();
    assert_eq!(warning_messages, native_warnings);
    assert!(
        result
            .warnings
            .iter()
            .all(|w| w.severity == "warning" && w.phase == "extract")
    );

    // dedup over the boundary, held-session flavor: a session holding the
    // extracted entries flags a re-import; a fuzzy near-miss (reworded
    // narration, same date/amount) must agree with the NATIVE canonical
    // matcher's verdict — not just degenerate identity inputs.
    let session = inst.rustledger_ledger_ledger().session();
    let handle = session.call_from_entries(&mut store, &result.entries)?;
    let flags = session.call_dedup(&mut store, handle, &result.entries)?;
    assert_eq!(flags, vec![true, true]);

    let mut reworded = result.entries.clone();
    let rustledger::ledger::types::Directive::Transaction(t) = &mut reworded[0] else {
        panic!("expected transaction");
    };
    t.narration = Some("Coffee Shop purchase".to_string());
    let component_flags = session.call_dedup(&mut store, handle, &reworded)?;
    // Native verdict on the same near-miss.
    let mut native_reworded = native.directives.clone();
    if let rustledger_core::Directive::Transaction(t) = &mut native_reworded[0] {
        t.narration = "Coffee Shop purchase".into();
    }
    let native_txns: Vec<_> = native
        .directives
        .iter()
        .filter_map(|d| match d {
            rustledger_core::Directive::Transaction(t) => Some(t.clone()),
            _ => None,
        })
        .collect();
    let native_flags: Vec<bool> = native_reworded
        .iter()
        .map(|d| match d {
            rustledger_core::Directive::Transaction(t) => rustledger_ops::dedup::is_duplicate(
                t,
                &native_txns,
                &rustledger_ops::dedup::FuzzyDedupConfig::default(),
            ),
            _ => false,
        })
        .collect();
    assert_eq!(
        component_flags, native_flags,
        "dedup drift vs native matcher"
    );

    // format-loaded renders the extracted entries to canonical text the
    // host can write into the ledger — closing the extract/review/save loop.
    let text = inst
        .rustledger_ledger_format()
        .call_format_loaded(&mut store, &result.entries)?
        .expect("renders");
    assert!(text.contains("Assets:Bank"), "{text}");
    Ok(())
}

/// `session.budget` (WIT 3.10.0): the component's budget over the held ledger
/// must equal the NATIVE `rustledger_budget` comparison over the same
/// interpolated, pad-expanded stream — the SAME composition the CLI's
/// `report budget` calls, so this pins the wasm surface against the CLI's
/// engine rather than a private re-implementation of the accrual.
///
/// The figures are `rust_decimal` (pure integer arithmetic), so they must match
/// byte-for-byte across the boundary; the `used` fractions are `f64` and are
/// compared within a tolerance.
#[test]
fn session_budget_matches_native_engine() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    // A leap February (the denominator that catches a naive 30-day month), a
    // child account (so `children` has something to aggregate), an income
    // target (so sign normalization and a second total bucket are exercised),
    // and one unreadable directive (so `errors` is non-empty).
    const LEDGER: &str = "\
option \"operating_currency\" \"USD\"
2024-01-01 open Expenses:Food
2024-01-01 open Expenses:Food:Restaurant
2024-01-01 open Income:Salary
2024-01-01 open Assets:Cash
2024-01-01 custom \"budget\" Expenses:Food \"monthly\" 400.00 USD
2024-01-01 custom \"budget\" Income:Salary \"monthly\" 5000.00 USD
2024-01-01 custom \"budget\" Expenses:Food \"decade\" 1.00 USD
2024-01-01 custom \"budget\" Expenses:Nosuch \"monthly\" 50.00 USD
2024-02-05 * \"groceries\"
  Expenses:Food  120.00 USD
  Assets:Cash
2024-02-06 * \"dinner\"
  Expenses:Food:Restaurant  80.00 USD
  Assets:Cash
2024-02-25 * \"pay\"
  Assets:Cash        4000.00 USD
  Income:Salary
";
    for children in [false, true] {
        // Component side: hold the ledger and ask for the budget over the boundary.
        let (mut store, inst) = instantiate()?;
        let session = inst.rustledger_ledger_ledger().session();
        let handle = session.call_constructor(&mut store, LEDGER)?;
        let via = session
            .call_budget(&mut store, handle, "2024-02-01", "2024-03-01", children, "")?
            .map_err(|e| anyhow::anyhow!("budget failed: {e}"))?;
        handle.resource_drop(&mut store)?;

        // Native reference: the same crate the CLI report runs.
        let native = rustledger_ffi_wasi::helpers::load_source(LEDGER);
        let padded = rustledger_booking::merge_with_padding(&native.directives);
        let types = rustledger_core::AccountTypes::default();
        let budgets = rustledger_budget::Budgets::from_directives(&padded);
        let want = budgets.compare(
            &padded,
            &types,
            "2024-02-01".parse().unwrap(),
            "2024-03-01".parse().unwrap(),
            children,
            None,
        );

        assert_eq!(via.rows.len(), want.rows.len(), "children={children}");
        for (got, want) in via.rows.iter().zip(&want.rows) {
            assert_eq!(got.account, want.account.as_str(), "children={children}");
            assert_eq!(got.currency, want.currency.as_str());
            assert_eq!(
                got.budgeted,
                want.budgeted.map(|d| d.to_string()),
                "budgeted for {} (children={children})",
                got.account
            );
            assert_eq!(got.actual, want.actual.map(|d| d.to_string()));
            assert_eq!(got.remaining, want.remaining().map(|d| d.to_string()));
            match (got.used, want.used_fraction()) {
                (Some(a), Some(b)) => assert!((a - b).abs() < 1e-12, "{a} vs {b}"),
                (a, b) => assert_eq!(a.is_none(), b.is_none(), "{a:?} vs {b:?}"),
            }
        }

        // Totals carry the account TYPE, lowercased, not the ledger's root name,
        // in the crate's CANONICAL order — beancount statement order, so income
        // precedes expenses. The CLI reorders for reading (the headline expenses
        // total leads); a host owns its own presentation, so the boundary hands
        // over the canonical sequence rather than the CLI's.
        assert_eq!(via.totals.len(), want.totals.len());
        let kinds: Vec<&str> = via.totals.iter().map(|t| t.kind.as_str()).collect();
        assert_eq!(kinds, vec!["income", "expenses"], "children={children}");
        // `kind` is a closed vocabulary; `root` carries the ledger's spelling.
        let roots: Vec<&str> = via.totals.iter().map(|t| t.root.as_str()).collect();
        assert_eq!(roots, vec!["Income", "Expenses"], "children={children}");

        // The component's error list must EQUAL the native one, not merely
        // contain a phrase from it. An existential check let the boundary emit
        // extra or duplicated warnings undetected, which is how the FFI came to
        // disagree with the CLI about which budgets deserved a complaint.
        let want: Vec<&str> = want.errors.iter().map(|e| e.reason.as_str()).collect();
        let got: Vec<String> = via
            .errors
            .iter()
            .map(|e| {
                e.message
                    .splitn(2, ": ")
                    .nth(1)
                    .unwrap_or(&e.message)
                    .to_string()
            })
            .collect();
        assert_eq!(got, want, "children={children}");
        assert!(!want.is_empty(), "the fixture must exercise some warning");
        assert!(via.errors.iter().all(|e| e.severity == "warning"));
        // ...including the report-level ones, not only parse failures.
        assert!(
            want.iter().any(|m| m.contains("no such account is opened")),
            "{want:?}"
        );
        // Rows exist, so there is no empty diagnosis to report.
        assert_eq!(via.empty, None, "children={children}");
    }
    Ok(())
}

/// The window is half-open and must be non-empty; a component has no clock, so
/// both bounds are required and a malformed one is an error rather than a
/// silently-substituted default.
#[test]
fn session_budget_rejects_an_empty_or_malformed_window() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let session = inst.rustledger_ledger_ledger().session();
    let handle = session.call_constructor(&mut store, "2024-01-01 open Expenses:Food\n")?;
    for (from, to, want) in [
        ("2024-03-01", "2024-03-01", "empty window"),
        ("2024-03-02", "2024-03-01", "empty window"),
        ("", "2024-03-01", "invalid from-date"),
        ("2024-03-01", "not-a-date", "invalid to-date"),
    ] {
        let err = session
            .call_budget(&mut store, handle, from, to, false, "")?
            .expect_err("must reject");
        assert!(err.contains(want), "for ({from}, {to}) got {err:?}");
    }
    handle.resource_drop(&mut store)?;
    Ok(())
}
