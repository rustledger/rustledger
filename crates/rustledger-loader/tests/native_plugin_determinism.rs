//! Every native plugin gives the same output every time it runs (#2625).
//!
//! Some native plugins emitted their output in hash-set order:
//! `capital_gains_classifier` inserted its new `open`s from a `HashSet`, and
//! `unrealized` reported its warnings in `HashMap` order, so the same ledger
//! loaded twice could come out different (and `split`/`merge` refused such
//! ledgers, because two loads disagreed). `std`'s `HashMap`/`HashSet` seed
//! every new map differently, even within one process, so running a plugin
//! several times here is enough to see the difference.
//!
//! Each native plugin in the registry has a ledger below that exercises it
//! (the test checks the plugin changes the load's output, so a fixture that
//! does nothing cannot pass), and the ledger is loaded `RUNS` times through
//! the real loader. Every load must render byte-identical directives and
//! errors. A plugin added to the registry without a fixture fails the test.

use rustledger_loader::{Ledger, LoadOptions, load};
use rustledger_plugin::NativePluginRegistry;
use std::fmt::Write as _;
use std::path::Path;

/// Loads per plugin. A `HashSet` of two elements comes out in the same order
/// by chance half the time; 16 loads make a hash-ordered plugin pass by luck
/// at most once in 2^15.
const RUNS: usize = 16;

/// A ledger exercising the named plugin. `docs` is a directory the
/// `document_discovery` fixture scans.
fn fixture(name: &str, docs: &Path) -> Option<String> {
    let src = match name {
        "auto_accounts" => "plugin \"beancount.plugins.auto_accounts\"\n\
             2024-01-01 * \"x\"\n  Expenses:Zeta  1 USD\n  Expenses:Alpha  2 USD\n  \
             Expenses:Mid  3 USD\n  Assets:Cash\n"
            .to_string(),
        "document_discovery" => format!(
            "option \"documents\" \"{}\"\n\
             plugin \"beancount.plugins.document_discovery\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Bank\n",
            docs.display()
        ),
        "implicit_prices" => "plugin \"beancount.plugins.implicit_prices\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock\n\
             2024-01-02 * \"buy\"\n  Assets:Stock  1 AAA {10 USD}\n  Assets:Stock  1 BBB {20 USD}\n  \
             Assets:Stock  1 CCC @ 30 USD\n  Assets:Cash\n"
            .to_string(),
        "check_commodity" => "plugin \"beancount.plugins.check_commodity\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock\n\
             2024-01-02 * \"x\"\n  Assets:Stock  1 AAA {1 USD}\n  Assets:Stock  1 BBB {1 USD}\n  \
             Assets:Stock  1 CCC {1 USD}\n  Assets:Cash\n"
            .to_string(),
        "auto_tag" => "plugin \"beancount.plugins.auto_tag\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food\n\
             2024-01-01 open Expenses:Travel\n\
             2024-01-02 * \"x\"\n  Expenses:Food  1 USD\n  Expenses:Travel  1 USD\n  Assets:Cash\n"
            .to_string(),
        "leafonly" => "plugin \"beancount.plugins.leafonly\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Cash:Sub\n\
             2024-01-01 open Expenses:Food\n2024-01-01 open Expenses:Food:Sub\n\
             2024-01-02 * \"x\"\n  Expenses:Food  1 USD\n  Expenses:Food:Sub  1 USD\n  Assets:Cash\n"
            .to_string(),
        "noduplicates" => "plugin \"beancount.plugins.noduplicates\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food\n\
             2024-01-02 * \"x\"\n  Expenses:Food  1 USD\n  Assets:Cash\n\
             2024-01-02 * \"x\"\n  Expenses:Food  1 USD\n  Assets:Cash\n"
            .to_string(),
        "onecommodity" => "plugin \"beancount.plugins.onecommodity\"\n\
             2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n2024-01-01 open Assets:Cash\n\
             2024-01-02 * \"x\"\n  Assets:A  1 AAA\n  Assets:A  1 BBB\n  Assets:B  1 CCC\n  \
             Assets:B  1 DDD\n  Assets:Cash  -1 AAA\n  Assets:Cash  -1 BBB\n  \
             Assets:Cash  -1 CCC\n  Assets:Cash  -1 DDD\n"
            .to_string(),
        "unique_prices" => "plugin \"beancount.plugins.unique_prices\"\n\
             2024-01-01 price AAA 1 USD\n2024-01-01 price AAA 2 USD\n\
             2024-01-01 price BBB 1 USD\n2024-01-01 price BBB 2 USD\n"
            .to_string(),
        "check_closing" => "plugin \"beancount.plugins.check_closing\"\n\
             2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n2024-01-01 open Assets:Cash\n\
             2024-01-02 * \"x\"\n  Assets:A  -1 AAA\n    closing: TRUE\n  \
             Assets:B  -1 BBB\n    closing: TRUE\n  Assets:Cash  1 AAA\n  Assets:Cash  1 BBB\n"
            .to_string(),
        "close_tree" => "plugin \"beancount.plugins.close_tree\"\n\
             2024-01-01 open Assets:P\n2024-01-01 open Assets:P:Zeta\n\
             2024-01-01 open Assets:P:Alpha\n2024-01-01 open Assets:P:Mid\n\
             2024-01-01 open Assets:P:Beta\n2024-02-01 close Assets:P\n"
            .to_string(),
        "coherent_cost" => "plugin \"beancount.plugins.coherent_cost\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock\n\
             2024-01-02 * \"x\"\n  Assets:Stock  1 AAA {1 USD}\n  Assets:Stock  1 BBB {1 USD}\n  \
             Assets:Cash\n\
             2024-01-03 * \"y\"\n  Assets:Stock  1 AAA\n  Assets:Stock  1 BBB\n  \
             Assets:Cash  -1 AAA\n  Assets:Cash  -1 BBB\n"
            .to_string(),
        "forecast" => "plugin \"beancount.plugins.forecast\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Power\n\
             2024-01-02 # \"Power [MONTHLY REPEAT 3 TIMES]\"\n  Expenses:Power  1 USD\n  \
             Assets:Cash\n"
            .to_string(),
        "sellgains" => "plugin \"beancount.plugins.sellgains\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock\n\
             2024-01-01 open Income:Gains\n\
             2024-01-02 * \"buy\"\n  Assets:Stock  10 AAA {10 USD}\n  Assets:Cash\n\
             2024-01-03 * \"sell, no gain posted\"\n  Assets:Stock  -10 AAA {10 USD} @ 12 USD\n  \
             Assets:Cash  100 USD\n"
            .to_string(),
        "pedantic" => "plugin \"beancount.plugins.pedantic\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Cash:Sub\n\
             2024-01-01 open Assets:A\n\
             2024-01-02 * \"x\"\n  Assets:Cash  1 USD\n  Assets:Cash:Sub  1 USD\n  \
             Assets:A  -2 USD\n  Assets:A  -1 EUR\n  Assets:Cash  1 EUR\n"
            .to_string(),
        "rx_txn_plugin" => "plugin \"beancount.plugins.rx_txn_plugin\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Rent\n\
             2024-01-02 * \"rent\" #rx_txn\n  Expenses:Rent  1 USD\n  Assets:Cash\n"
            .to_string(),
        "split_expenses" => "plugin \"beancount.plugins.split_expenses\" \"Martin Caroline\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food\n\
             2024-01-01 open Expenses:Travel\n\
             2024-01-02 * \"x\"\n  Expenses:Food  10 USD\n  Expenses:Travel  10 USD\n  \
             Assets:Cash\n"
            .to_string(),
        "unrealized" => "plugin \"beancount.plugins.unrealized\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:A\n2024-01-01 open Assets:B\n\
             2024-01-01 open Assets:C\n\
             2024-01-02 * \"buy\"\n  Assets:A  1 AAA {10 USD}\n  Assets:A  1 BBB {10 USD}\n  \
             Assets:B  1 AAA {10 USD}\n  Assets:B  1 CCC {10 USD}\n  Assets:C  1 BBB {10 USD}\n  \
             Assets:C  1 CCC {10 USD}\n  Assets:Cash\n\
             2024-01-03 price AAA 20 USD\n2024-01-03 price BBB 30 USD\n\
             2024-01-03 price CCC 40 USD\n"
            .to_string(),
        "nounused" => "plugin \"beancount.plugins.nounused\"\n\
             2024-01-01 open Assets:Zeta\n2024-01-01 open Assets:Alpha\n\
             2024-01-01 open Assets:Mid\n"
            .to_string(),
        "check_drained" => "plugin \"beancount.plugins.check_drained\"\n\
             2024-01-01 open Assets:A\n2024-01-01 open Assets:Cash\n\
             2024-01-02 * \"x\"\n  Assets:A  1 AAA\n  Assets:A  1 BBB\n  Assets:A  1 CCC\n  \
             Assets:Cash  -1 AAA\n  Assets:Cash  -1 BBB\n  Assets:Cash  -1 CCC\n\
             2024-01-03 * \"y\"\n  Assets:A  -1 AAA\n  Assets:A  -1 BBB\n  Assets:A  -1 CCC\n  \
             Assets:Cash  1 AAA\n  Assets:Cash  1 BBB\n  Assets:Cash  1 CCC\n\
             2024-01-04 close Assets:A\n"
            .to_string(),
        "commodity_attr" => "plugin \"beancount.plugins.commodity_attr\" \
             \"{'name': None, 'sector': ('Tech', 'Finance')}\"\n\
             2024-01-01 commodity AAA\n2024-01-01 commodity BBB\n  sector: \"Food\"\n\
             2024-01-01 commodity CCC\n  name: \"C\"\n"
            .to_string(),
        "check_average_cost" => "plugin \"beancount.plugins.check_average_cost\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Stock \"NONE\"\n\
             2024-01-02 * \"buy\"\n  Assets:Stock  10 AAA {10 USD}\n  Assets:Cash\n\
             2024-01-03 * \"buy\"\n  Assets:Stock  10 AAA {20 USD}\n  Assets:Cash\n\
             2024-01-04 * \"sell\"\n  Assets:Stock  -5 AAA {10 USD}\n  Assets:Cash\n"
            .to_string(),
        "currency_accounts" => "plugin \"beancount.plugins.currency_accounts\" \"Equity:Trading\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Euro\n\
             2024-01-01 open Assets:Pound\n\
             2024-01-02 * \"x\"\n  Assets:Euro  10 EUR @ 1.1 USD\n  Assets:Pound  10 GBP @ 1.3 USD\n  \
             Assets:Cash  -24 USD\n"
            .to_string(),
        // `Assets:ZA`'s target is `Assets:ZB`, itself a zerosum account, so
        // the order the accounts are matched in decides the result.
        "zerosum" => "plugin \"beancount.plugins.zerosum\" \
             \"{'zerosum_accounts': {'Assets:ZA': ('Assets:ZB', 30), \
             'Assets:ZB': ('Assets:ZB-Matched', 30)}}\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:ZA\n2024-01-01 open Assets:ZB\n\
             2024-01-02 * \"out\"\n  Assets:ZA  10 USD\n  Assets:ZB  5 USD\n  Assets:Cash\n\
             2024-01-03 * \"in\"\n  Assets:ZA  -10 USD\n  Assets:ZB  -5 USD\n  Assets:Cash\n"
            .to_string(),
        "effective_date" => "plugin \"beancount.plugins.effective_date\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Rent\n\
             2024-01-01 open Expenses:Insurance\n\
             2024-01-02 * \"x\"\n  Expenses:Rent  10 USD\n    effective_date: 2024-02-01\n  \
             Expenses:Insurance  10 USD\n    effective_date: 2024-03-01\n  Assets:Cash\n"
            .to_string(),
        "generate_base_ccy_prices" => {
            "plugin \"beancount.plugins.generate_base_ccy_prices\" \"USD\"\n\
             2024-01-01 commodity AAA\n  price: \"EUR:yahoo/AAA\"\n\
             2024-01-01 commodity BBB\n  price: \"GBP:yahoo/BBB\"\n\
             2024-01-01 price EUR 1.1 USD\n2024-01-01 price GBP 1.3 USD\n\
             2024-01-02 price AAA 10 EUR\n2024-01-02 price BBB 10 GBP\n"
                .to_string()
        }
        "rename_accounts" => "plugin \"beancount.plugins.rename_accounts\" \
             \"{'Expenses:Food': 'Expenses:Dining', 'Expenses:Car': 'Expenses:Auto'}\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Expenses:Food\n\
             2024-01-01 open Expenses:Car\n\
             2024-01-02 * \"x\"\n  Expenses:Food  1 USD\n  Expenses:Car  1 USD\n  Assets:Cash\n"
            .to_string(),
        "valuation" => "plugin \"beancount.plugins.valuation\"\n\
             2024-01-01 open Assets:Cash\n\
             2024-01-01 open Assets:FundA \"FIFO\"\n2024-01-01 open Income:FundA:PnL\n\
             2024-01-01 open Assets:FundB \"FIFO\"\n2024-01-01 open Income:FundB:PnL\n\
             2024-01-01 open Assets:FundC \"FIFO\"\n2024-01-01 open Income:FundC:PnL\n\
             2024-01-01 custom \"valuation\" \"config\"\n  account: \"Assets:FundA\"\n  \
             currency: \"FUNDA\"\n  pnlAccount: \"Income:FundA:PnL\"\n\
             2024-01-01 custom \"valuation\" \"config\"\n  account: \"Assets:FundB\"\n  \
             currency: \"FUNDB\"\n  pnlAccount: \"Income:FundB:PnL\"\n\
             2024-01-01 custom \"valuation\" \"config\"\n  account: \"Assets:FundC\"\n  \
             currency: \"FUNDC\"\n  pnlAccount: \"Income:FundC:PnL\"\n\
             2024-01-02 * \"in\"\n  Assets:FundA  100 USD\n  Assets:FundB  100 USD\n  \
             Assets:FundC  100 USD\n  Assets:Cash\n"
            .to_string(),
        "long_short" => "plugin \"beancount_reds_plugins.capital_gains_classifier.long_short\" \
             \"{'Income.*:Capital-Gains': [':Capital-Gains', ':Capital-Gains:Short', \
             ':Capital-Gains:Long']}\"\n\
             2020-01-01 open Assets:Cash\n2020-01-01 open Assets:Stock\n\
             2020-01-01 open Income:Capital-Gains\n\
             2020-01-02 * \"buy\"\n  Assets:Stock  10 AAA {10 USD}\n  Assets:Cash\n\
             2024-01-02 * \"buy\"\n  Assets:Stock  10 AAA {11 USD}\n  Assets:Cash\n\
             2024-02-01 * \"sell\"\n  Assets:Stock  -10 AAA {10 USD, 2020-01-02} @ 20 USD\n  \
             Assets:Stock  -10 AAA {11 USD, 2024-01-02} @ 20 USD\n  Assets:Cash  400 USD\n  \
             Income:Capital-Gains  -190 USD\n"
            .to_string(),
        "gain_loss" => "plugin \"beancount_reds_plugins.capital_gains_classifier.gain_loss\" \
             \"{'Income.*:Capital-Gains': [':Capital-Gains', ':Capital-Gains:Gains', \
             ':Capital-Gains:Losses']}\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Income:A:Capital-Gains\n\
             2024-01-01 open Income:B:Capital-Gains\n\
             2024-01-02 * \"x\"\n  Income:A:Capital-Gains  -10 USD\n  \
             Income:B:Capital-Gains  5 USD\n  Assets:Cash\n"
            .to_string(),
        "box_accrual" => "plugin \"beancount_reds_plugins.box_accrual.box_accrual\"\n\
             2024-01-01 open Assets:Broker\n2024-01-01 open Income:Capital-Losses\n\
             2024-01-15 * \"Sell synthetic\"\n  synthetic_loan_expiry: 2026-06-30\n  \
             Assets:Broker  -500 USD\n  Income:Capital-Losses  500 USD\n"
            .to_string(),
        _ => return None,
    };
    Some(src)
}

/// Everything a load produces that a user can see, rendered to one string.
fn render(ledger: &Ledger) -> String {
    let mut out = String::new();
    for d in &ledger.directives {
        writeln!(out, "{d:?}").unwrap();
    }
    for e in &ledger.errors {
        writeln!(out, "{e:?}").unwrap();
    }
    out
}

/// The rendering with the ledger's own path taken out: the two ledgers
/// compared differ in name, and an error naming its file would otherwise
/// tell them apart whatever the plugin did.
fn load_rendered(path: &Path) -> String {
    render(&load(path, &LoadOptions::default()).expect("the fixture loads"))
        .replace(&path.display().to_string(), "<ledger>")
}

#[test]
fn every_native_plugin_gives_identical_output_on_every_run() {
    let docs = tempfile::tempdir().expect("create document dir");
    // Several documents and an unopened account, so the scan finds files in
    // more than one directory and reports one.
    for rel in [
        "Assets/Cash/2024-01-05.zeta.pdf",
        "Assets/Cash/2024-01-03.alpha.pdf",
        "Assets/Cash/2024-01-04.mid.pdf",
        "Assets/Bank/2024-01-02.b.pdf",
        "Assets/Bank/2024-01-01.a.pdf",
        "Assets/Unknown/2024-01-01.u.pdf",
        "Assets/Other/2024-01-01.o.pdf",
    ] {
        let p = docs.path().join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, b"").unwrap();
    }

    let dir = tempfile::tempdir().expect("create ledger dir");
    let mut missing = Vec::new();
    let mut idle = Vec::new();
    let mut unstable = Vec::new();
    let mut checked = 0;
    for plugin in NativePluginRegistry::global().iter() {
        let name = plugin.name();
        let Some(source) = fixture(name, docs.path()) else {
            missing.push(name);
            continue;
        };
        let with = dir.path().join(format!("{name}.beancount"));
        std::fs::write(&with, &source).unwrap();
        // The same ledger without what runs the plugin (its `plugin` line,
        // and for `document_discovery` the `documents` option): the fixture
        // must make the plugin change something, or this test proves nothing
        // about it. Each such line becomes a comment of the same length, so
        // every other directive keeps its span and only the plugin's effect
        // can tell the two loads apart.
        let without = dir.path().join(format!("{name}-without.beancount"));
        let mut stripped = String::new();
        for line in source.lines() {
            if line.starts_with("plugin ") || line.starts_with("option \"documents\"") {
                writeln!(stripped, ";{}", " ".repeat(line.len() - 1)).unwrap();
            } else {
                writeln!(stripped, "{line}").unwrap();
            }
        }
        std::fs::write(&without, stripped).unwrap();

        let first = load_rendered(&with);
        if first == load_rendered(&without) {
            idle.push(name);
            continue;
        }
        if (1..RUNS).any(|_| load_rendered(&with) != first) {
            unstable.push(name);
        }
        checked += 1;
    }

    assert!(
        missing.is_empty(),
        "native plugins with no fixture here (add one): {missing:?}"
    );
    assert!(
        idle.is_empty(),
        "these fixtures do not exercise their plugin (the output is the same without it): {idle:?}"
    );
    assert!(
        unstable.is_empty(),
        "these native plugins gave different output across {RUNS} loads of the same ledger: {unstable:?}"
    );
    assert_eq!(checked, NativePluginRegistry::global().iter().count());
}

/// `document_discovery` walks a directory's files before its subdirectories,
/// each by name, as beancount's `account.walk` does (#2625).
///
/// `read_dir` yields entries in the filesystem's own order (hash order on
/// ext4, reverse creation order on tmpfs), which is stable within one process
/// and so invisible to the test above, but differs between machines.
#[test]
fn document_discovery_walks_files_then_subdirectories_by_name() {
    let docs = tempfile::tempdir().expect("create document dir");
    // Created out of order, so no filesystem's own order is the sorted one.
    let names = [
        "m", "c", "x", "a", "q", "f", "z", "b", "k", "e", "w", "h", "p", "d", "y",
    ];
    for name in names {
        let p = docs
            .path()
            .join(format!("Assets/Cash/2024-01-01.{name}.pdf"));
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, b"").unwrap();
    }
    // A subaccount whose name (`0Sub`, '0' < '2') sorts before the dated
    // files: it still comes after them, as `os.walk` visits a directory's
    // files before descending.
    let sub = docs.path().join("Assets/Cash/0Sub/2024-01-01.sub.pdf");
    std::fs::create_dir_all(sub.parent().unwrap()).unwrap();
    std::fs::write(&sub, b"").unwrap();

    let dir = tempfile::tempdir().expect("create ledger dir");
    let file = dir.path().join("docs.beancount");
    std::fs::write(
        &file,
        format!(
            "option \"documents\" \"{}\"\n\
             plugin \"beancount.plugins.document_discovery\"\n\
             2024-01-01 open Assets:Cash\n2024-01-01 open Assets:Cash:0Sub\n",
            docs.path().display()
        ),
    )
    .unwrap();
    let ledger = load(&file, &LoadOptions::default()).expect("the fixture loads");
    let found: Vec<String> = ledger
        .directives
        .iter()
        .filter_map(|d| match &d.value {
            rustledger_core::Directive::Document(doc) => Path::new(doc.path.as_str())
                .file_name()
                .map(|n| n.to_string_lossy().into_owned()),
            _ => None,
        })
        .collect();
    let mut expected: Vec<String> = names
        .iter()
        .map(|n| format!("2024-01-01.{n}.pdf"))
        .collect();
    expected.sort();
    expected.push("2024-01-01.sub.pdf".to_string());
    assert_eq!(found, expected);
}

/// `zerosum` matches its accounts in the order the config lists them, as
/// `beancount_reds_plugins` walks its `zerosum_accounts` dict (#2625).
///
/// `Assets:ZA`'s matches are renamed to `Assets:ZB`, itself a zerosum account
/// listed after it, so they are then matched again under `Assets:ZB` and end
/// in `Assets:ZB-Matched` with `Assets:ZB`'s own postings. Matching `Assets:ZB`
/// first would leave `Assets:ZA`'s postings in `Assets:ZB`, unmatched.
///
/// beancount 3.2 with `beancount_reds_plugins` zerosum puts all four postings
/// in `Assets:ZB-Matched` too (it moves each rewritten posting to the end of
/// its transaction, a known divergence documented in `zerosum.rs`).
#[test]
fn zerosum_matches_accounts_in_config_order() {
    let dir = tempfile::tempdir().expect("create ledger dir");
    let file = dir.path().join("zerosum.beancount");
    std::fs::write(&file, fixture("zerosum", dir.path()).unwrap()).unwrap();
    // Repeated: in hash order the right answer came out half the time.
    for _ in 0..RUNS {
        let ledger = load(&file, &LoadOptions::default()).expect("the fixture loads");
        let accounts: Vec<String> = ledger
            .directives
            .iter()
            .filter_map(|d| match &d.value {
                rustledger_core::Directive::Transaction(t) => Some(t),
                _ => None,
            })
            .flat_map(|t| t.postings.iter().map(|p| p.account.to_string()))
            .filter(|a| a != "Assets:Cash")
            .collect();
        assert_eq!(accounts, ["Assets:ZB-Matched"; 4]);
    }
}
