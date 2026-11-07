//! Every WASM query entry point resolves the source-location columns and
//! `#balances.discrepancy` (#2823, #2825).
//!
//! These read NULL on every WASM path: each built a bare executor with no
//! source map and no discrepancies, where the CLI set both up. All paths now
//! go through `Executor::for_ledger`. Expected values are bean-query's
//! (beanquery 0.2.0): `location` is `path:line:`, and an in-memory source is
//! named `<string>`, as beancount's `load_string` names it.

#![cfg(target_arch = "wasm32")]

use wasm_bindgen::JsValue;
use wasm_bindgen_test::*;

const LEDGER: &str = "2024-01-01 open Assets:Bank
2024-01-01 open Equity:Opening
2024-01-02 *
  Assets:Bank     10 USD
  Equity:Opening
2024-01-05 balance Assets:Bank 999.00 USD
";

fn get_field(obj: &JsValue, field: &str) -> JsValue {
    js_sys::Reflect::get(obj, &JsValue::from_str(field)).unwrap_or(JsValue::UNDEFINED)
}

/// Row 0 of `result`, after checking the query raised no error.
fn first_row(result: &JsValue, query: &str) -> js_sys::Array {
    let rows = js_sys::Array::from(&get_field(result, "rows"));
    assert!(rows.length() > 0, "{query}: no rows");
    js_sys::Array::from(&rows.get(0))
}

fn string_cell(row: &js_sys::Array, i: u32) -> String {
    row.get(i)
        .as_string()
        .unwrap_or_else(|| panic!("cell {i} is not a string: {:?}", row.get(i)))
}

fn number_cell(row: &js_sys::Array, i: u32) -> f64 {
    row.get(i)
        .as_f64()
        .unwrap_or_else(|| panic!("cell {i} is not a number: {:?}", row.get(i)))
}

/// Check one surface: `query` runs a query on [`LEDGER`] loaded as `name`.
fn check(query: impl Fn(&str) -> JsValue, name: &str) {
    let q = "SELECT filename, lineno, location FROM postings LIMIT 1";
    let row = first_row(&query(q), q);
    assert_eq!(string_cell(&row, 0), name, "{name}: filename");
    assert_eq!(number_cell(&row, 1), 4.0, "{name}: lineno");
    assert_eq!(
        string_cell(&row, 2),
        format!("{name}:4:"),
        "{name}: location"
    );

    let q = "SELECT meta('lineno'), entry_meta('filename') LIMIT 1";
    let row = first_row(&query(q), q);
    assert_eq!(number_cell(&row, 0), 4.0, "{name}: meta('lineno')");
    assert_eq!(string_cell(&row, 1), name, "{name}: entry_meta('filename')");

    // bean-query: `Assets:Bank, -989.00 USD` (10 held, 999.00 asserted).
    let q = "SELECT account, discrepancy FROM #balances";
    let row = first_row(&query(q), q);
    let amount = row.get(1);
    assert_eq!(
        get_field(&amount, "number").as_string().as_deref(),
        Some("-989.00"),
        "{name}: discrepancy {amount:?}"
    );
    assert_eq!(
        get_field(&amount, "currency").as_string().as_deref(),
        Some("USD"),
        "{name}: discrepancy currency"
    );
}

#[wasm_bindgen_test]
fn query_resolves_sources_and_discrepancy() {
    check(
        |q| rustledger_wasm::query(LEDGER, q).expect("query"),
        "<string>",
    );
}

#[wasm_bindgen_test]
fn parsed_ledger_resolves_sources_and_discrepancy() {
    let ledger = rustledger_wasm::ParsedLedger::new(LEDGER);
    check(|q| ledger.query(q).expect("query"), "<string>");
}

#[wasm_bindgen_test]
fn parsed_ledger_from_cache_resolves_sources_and_discrepancy() {
    let bytes = rustledger_wasm::ParsedLedger::new(LEDGER)
        .serialize()
        .expect("serialize");
    let ledger = rustledger_wasm::ParsedLedger::from_cache(&bytes, LEDGER).expect("from cache");
    check(|q| ledger.query(q).expect("query"), "<string>");
}

fn files() -> JsValue {
    let files = js_sys::Object::new();
    js_sys::Reflect::set(
        &files,
        &JsValue::from_str("main.beancount"),
        &JsValue::from_str(LEDGER),
    )
    .expect("set");
    files.into()
}

#[wasm_bindgen_test]
fn query_multi_file_resolves_sources_and_discrepancy() {
    check(
        |q| rustledger_wasm::query_multi_file(files(), "main.beancount", q).expect("query"),
        "main.beancount",
    );
}

#[wasm_bindgen_test]
fn ledger_from_files_resolves_sources_and_discrepancy() {
    let ledger =
        rustledger_wasm::Ledger::from_files(files(), "main.beancount").expect("from files");
    check(|q| ledger.query(q).expect("query"), "main.beancount");
}

/// A directive a plugin created names the plugin, fresh and restored from
/// the cache alike (bean-query: `open`, `<auto_accounts>`, 0 and 1). A
/// restored ledger read NULL: its source map lost the placeholders.
#[wasm_bindgen_test]
fn parsed_ledger_names_the_plugin_that_created_a_directive_after_the_cache() {
    let source = "plugin \"beancount.plugins.auto_accounts\"

2024-01-02 *
  Assets:Bank     10 USD
  Equity:Opening
";
    let q = "SELECT type, filename, lineno FROM #entries WHERE type = 'open' ORDER BY lineno";
    let rows = |ledger: &rustledger_wasm::ParsedLedger| -> Vec<(String, String, f64)> {
        let rows = js_sys::Array::from(&get_field(&ledger.query(q).expect("query"), "rows"));
        rows.iter()
            .map(|row| {
                let row = js_sys::Array::from(&row);
                (
                    string_cell(&row, 0),
                    string_cell(&row, 1),
                    number_cell(&row, 2),
                )
            })
            .collect()
    };
    let want = vec![
        ("open".to_string(), "<auto_accounts>".to_string(), 0.0),
        ("open".to_string(), "<auto_accounts>".to_string(), 1.0),
    ];
    let fresh = rustledger_wasm::ParsedLedger::new(source);
    assert_eq!(rows(&fresh), want, "fresh");
    let bytes = fresh.serialize().expect("serialize");
    let restored = rustledger_wasm::ParsedLedger::from_cache(&bytes, source).expect("from cache");
    assert_eq!(rows(&restored), want, "restored");
}

/// `queryMultiFile` answers over an include cycle and over an include glob
/// matching nothing, as bean-query does: no load error but a parse error stops
/// a query (`LoadError::blocks_queries`, #2861). It returned no rows.
#[wasm_bindgen_test]
fn query_multi_file_answers_over_a_cycle_and_an_empty_glob() {
    let cases = [
        (
            "include \"txn.beancount\"\n",
            "include \"main.beancount\"\n",
        ),
        (
            "include \"txn.beancount\"\ninclude \"missing/*.beancount\"\n",
            "",
        ),
    ];
    for (includes, txn_tail) in cases {
        let files = js_sys::Object::new();
        let set = |name: &str, text: String| {
            js_sys::Reflect::set(&files, &JsValue::from_str(name), &JsValue::from_str(&text))
                .expect("set");
        };
        set(
            "main.beancount",
            format!("2024-01-01 open Assets:Bank\n2024-01-01 open Equity:Opening\n{includes}"),
        );
        set(
            "txn.beancount",
            format!("2024-01-02 *\n  Assets:Bank     10 USD\n  Equity:Opening\n{txn_tail}"),
        );
        let q = "SELECT filename, lineno FROM postings LIMIT 1";
        let result =
            rustledger_wasm::query_multi_file(files.into(), "main.beancount", q).expect("query");
        let row = first_row(&result, includes);
        assert_eq!(string_cell(&row, 0), "txn.beancount", "{includes}");
        assert_eq!(number_cell(&row, 1), 2.0, "{includes}");
        let errors = js_sys::Array::from(&get_field(&result, "errors"));
        assert_eq!(errors.length(), 1, "{includes}: {errors:?}");
    }
}

/// The WASM side of the drift guard for the rule for whether a file-based
/// query answers despite load errors (#2861). `queryMultiFile` and
/// `Ledger.fromFiles` give exactly the rows the loader, CLI and FFI tests
/// expect on the same ledgers, or refuse, reporting the same load error.
/// Neither confines includes (an in-memory filesystem has no tree to escape:
/// `root/../other.beancount` is the key `other.beancount`, which is read), so
/// they run the unconfined cases; the cases needing a real filesystem (a
/// directory, a file to decrypt) are skipped. `queryMultiFile` refused over a
/// missing include, and `Ledger.query` answered over a parse or booking error.
mod query_answer_rule {
    include!("../../rustledger-loader/tests/query_answer_rule/cases.rs");

    use super::get_field;
    use wasm_bindgen::JsValue;
    use wasm_bindgen_test::*;

    fn files(case: &QueryRuleCase) -> JsValue {
        let files = js_sys::Object::new();
        for (path, text) in case.files {
            js_sys::Reflect::set(&files, &JsValue::from_str(path), &JsValue::from_str(text))
                .expect("set");
        }
        files.into()
    }

    /// `result` is exactly `case`'s answer: its rows (under the query's one
    /// column), or a refusal (no columns), with its load error among the
    /// result's own `errors`. Every surface reports its load's errors in the
    /// result, refusing or answering (#2882): a refusal is told from an answer
    /// with no rows by its columns, which a ledger that failed to parse, and
    /// so has no entries, would otherwise answer with.
    fn check(case: &QueryRuleCase, surface: &str, result: &JsValue) {
        let columns: Vec<String> = js_sys::Array::from(&get_field(result, "columns"))
            .iter()
            .map(|c| c.as_string().unwrap_or_default())
            .collect();
        let rows: Vec<String> = js_sys::Array::from(&get_field(result, "rows"))
            .iter()
            .map(|row| {
                let row = js_sys::Array::from(&row);
                assert_eq!(row.length(), 1, "{} via {surface}", case.name);
                row.get(0)
                    .as_string()
                    .unwrap_or_else(|| panic!("{} via {surface}: not text", case.name))
            })
            .collect();
        let errors: Vec<String> = js_sys::Array::from(&get_field(result, "errors"))
            .iter()
            .map(|e| get_field(&e, "message").as_string().unwrap_or_default())
            .collect();
        let context = format!(
            "{} via {surface}: columns {columns:?}, rows {rows:?}, errors {errors:?}",
            case.name
        );
        match case.rows {
            Some(want) => {
                assert_eq!(columns, ["narration"], "{context}");
                assert_eq!(rows, want, "{context}");
            }
            None => {
                assert!(columns.is_empty(), "a refusal has no columns: {context}");
                assert!(rows.is_empty(), "{context}");
                assert!(!errors.is_empty(), "{context}");
            }
        }
        if let Some(error) = case.error {
            assert!(
                errors.iter().any(|m| m.contains(error)),
                "`{error}` not reported: {context}"
            );
        }
    }

    #[wasm_bindgen_test]
    fn query_surfaces_answer_or_refuse_by_the_shared_rule() {
        for case in QUERY_RULE_CASES {
            if case.disk_only || case.confinement == Confinement::ConfinedOnly {
                continue;
            }
            let result =
                rustledger_wasm::query_multi_file(files(case), case.entry, QUERY_RULE_QUERY)
                    .expect("queryMultiFile");
            check(case, "queryMultiFile", &result);

            let ledger =
                rustledger_wasm::Ledger::from_files(files(case), case.entry).expect("fromFiles");
            check(
                case,
                "Ledger.query",
                &ledger.query(QUERY_RULE_QUERY).expect("query"),
            );
            let restored = rustledger_wasm::Ledger::from_cache(&ledger.serialize().expect("ser"))
                .expect("fromCache");
            check(
                case,
                "Ledger.query from cache",
                &restored.query(QUERY_RULE_QUERY).expect("query"),
            );
        }
    }

    /// The source-text surfaces follow the same rule (#2882) on the cases
    /// whose ledger is one file: `query(source)`, and `ParsedLedger.query`
    /// fresh and from cache. `query` refused on any severity-error, and
    /// `ParsedLedger.query` on any load error, so both returned no rows over
    /// the plugin-error case.
    #[wasm_bindgen_test]
    fn source_query_surfaces_answer_or_refuse_by_the_shared_rule() {
        let mut ran = 0;
        for case in QUERY_RULE_CASES.iter().filter(|c| c.source_text) {
            ran += 1;
            let source = case
                .files
                .iter()
                .find(|(path, _)| *path == case.entry)
                .expect("the entry file")
                .1;
            let result = rustledger_wasm::query(source, QUERY_RULE_QUERY).expect("query");
            check(case, "query", &result);

            let ledger = rustledger_wasm::ParsedLedger::new(source);
            check(
                case,
                "ParsedLedger.query",
                &ledger.query(QUERY_RULE_QUERY).expect("query"),
            );
            let restored = rustledger_wasm::ParsedLedger::from_cache(
                &ledger.serialize().expect("serialize"),
                source,
            )
            .expect("fromCache");
            check(
                case,
                "ParsedLedger.query from cache",
                &restored.query(QUERY_RULE_QUERY).expect("query"),
            );
        }
        assert!(ran >= 4, "only {ran} source-text cases");
    }

    /// An `include` in source text has no file to read, and is reported as
    /// missing; `query(source)` answers over it, as over a missing include
    /// in a file (#2882). It refused, the error being severity-error.
    #[wasm_bindgen_test]
    fn source_query_answers_over_an_unresolved_include() {
        let source = concat!(
            "include \"other.beancount\"\n",
            "2024-01-01 open Assets:Cash\n2024-01-01 open Income:Salary\n",
            "2024-01-02 * \"pay\"\n  Assets:Cash  100 USD\n  Income:Salary\n",
        );
        let case = QueryRuleCase {
            name: "include in source text",
            entry: "main.beancount",
            files: &[],
            rows: Some(&["pay"]),
            error: Some("other.beancount"),
            confinement: Confinement::Any,
            disk_only: false,
            source_text: true,
        };
        let result = rustledger_wasm::query(source, QUERY_RULE_QUERY).expect("query");
        check(&case, "query", &result);
        let ledger = rustledger_wasm::ParsedLedger::new(source);
        check(
            &case,
            "ParsedLedger.query",
            &ledger.query(QUERY_RULE_QUERY).expect("query"),
        );
    }
}

/// `queryWithHost` treats a `readFile` that throws an error whose `code` is
/// set and is not `ENOENT` as a file the host could not read, which stops the
/// query, as `rledger query` and bean-query refuse an include they cannot read
/// (#2861). Every such throw was "not found", so the query answered without
/// the file. A throw with no `code`, an `ENOENT` one and a `null` return stay
/// a missing file, which the query answers over: the contract these entry
/// points shipped with (v0.22.0).
#[wasm_bindgen_test]
fn query_with_host_refuses_an_include_the_host_cannot_read() {
    // `missing` is the JS the host runs for any path but the entry file.
    let run = |missing: &str| {
        let read_file = js_sys::Function::new_with_args(
            "p",
            &format!(
                "if (p.endsWith('main.beancount')) {{ return 'include \"sub.beancount\"\\n\
                 2024-01-01 open Assets:Cash\\n2024-01-01 open Income:Salary\\n\
                 2024-01-02 * \"pay\"\\n  Assets:Cash  100 USD\\n  Income:Salary\\n'; }}\
                 {missing}"
            ),
        );
        let host = js_sys::Object::new();
        js_sys::Reflect::set(&host, &JsValue::from_str("readFile"), &read_file).expect("set");
        let q = "SELECT narration FROM postings WHERE account = 'Assets:Cash'";
        rustledger_wasm::query_with_host(&host.into(), "main.beancount", q).expect("query")
    };

    for code in ["EACCES", "EISDIR"] {
        let refused = run(&format!(
            "const e = new Error('cannot read ' + p); e.code = '{code}'; throw e;"
        ));
        let rows = js_sys::Array::from(&get_field(&refused, "rows"));
        assert_eq!(rows.length(), 0, "{code}");
        let errors = js_sys::Array::from(&get_field(&refused, "errors"));
        assert!(
            errors.length() > 0,
            "{code}: the unreadable include is reported"
        );
    }

    for (label, missing) in [
        (
            "ENOENT",
            "const e = new Error('no such file ' + p); e.code = 'ENOENT'; throw e;",
        ),
        ("a throw without a code", "throw new Error('not found');"),
        ("null", "return null;"),
    ] {
        let answered = run(missing);
        let row = first_row(&answered, label);
        assert_eq!(string_cell(&row, 0), "pay", "{label}");
        let errors = js_sys::Array::from(&get_field(&answered, "errors"));
        assert!(
            errors.length() > 0,
            "{label}: the missing include is reported"
        );
    }
}
