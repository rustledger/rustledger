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
use wasmtime_wasi::{DirPerms, FilePerms, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

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

fn component_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/wasm32-wasip2/debug/rustledger_ffi_component.wasm")
}

fn instantiate() -> Result<(Store<Host>, Rustledger)> {
    let engine = Engine::default();
    let component = Component::from_file(&engine, component_path())?;
    let mut linker = Linker::<Host>::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;
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
    let wasi = WasiCtxBuilder::new()
        .preopened_dir(host_dir, "/work", DirPerms::READ, FilePerms::READ)?
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

#[test]
fn version_matches() -> Result<()> {
    if !component_path().exists() {
        eprintln!("skip: component wasm not built");
        return Ok(());
    }
    let (mut store, inst) = instantiate()?;
    let version = inst.rustledger_ledger_ledger().call_version(&mut store)?;
    assert_eq!(version, "2.1");
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
        .call_load(&mut store, LEDGER)?;
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
    let loaded = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, LEDGER_WITH_HISTORY)?;
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
    let loaded = inst.rustledger_ledger_ledger().call_load(&mut store, src)?;
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
    let loaded = inst.rustledger_ledger_ledger().call_load(&mut store, src)?;
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
    let r =
        inst.rustledger_ledger_ledger()
            .call_load_file(&mut store, "/work/main.bean", true, &[])?;
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
    let without =
        inst.rustledger_ledger_ledger()
            .call_load_file(&mut store, "/work/main.bean", true, &[])?;
    let with = inst.rustledger_ledger_ledger().call_load_file(
        &mut store,
        "/work/main.bean",
        true,
        &["implicit_prices".to_string()],
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
    let loaded = inst
        .rustledger_ledger_ledger()
        .call_load(&mut store, AUTO_ACCOUNTS_LEDGER)?;
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
    let loaded =
        inst.rustledger_ledger_ledger()
            .call_load_file(&mut store, "/work/main.bean", true, &[])?;
    assert_generated_opens(&loaded.entries, "component load_file");
    Ok(())
}
