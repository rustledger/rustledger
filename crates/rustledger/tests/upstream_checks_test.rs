//! Every check beancount can report is accounted for, and the table that
//! says so is true.
//!
//! `tests/fixtures/upstream-checks/checks.toml` has one row per check
//! beancount 3.2.3 can report to a user (an error site in `ops/`, `parser/`,
//! `core/` or `loader.py`, an exception it turns into an error, a plugin
//! module, a deprecated option), with rledger's status for it: `covered`,
//! `deviation`, `not-applicable` or `missing`. See
//! `docs/reference/upstream-checks.md`.
//!
//! Four tests keep it honest:
//!
//! * [`upstream_checks_table_is_well_formed`]: every row has what its status
//!   requires, every case file and named test exists, every deviation links a
//!   heading of `docs/reference/compatibility.md`.
//! * [`upstream_checks_rledger_matches_the_table`]: each row's case ledger,
//!   run through `rledger check`, reports the row's code on exactly the
//!   row's lines (or reports nothing, for a row without a code).
//! * [`upstream_checks_beancount_matches_the_table`]: the same ledger, run
//!   through beancount's `bean-check`, reports the row's message on exactly
//!   the row's lines. A row passes only when both sides do, so "covered"
//!   means "the same lines", or the row says why not.
//! * [`upstream_checks_table_lists_every_upstream_check`]: the drift guard.
//!   `enumerate.py` lists the checks in the INSTALLED beancount; any it
//!   finds that the table lacks (or the table lists that it no longer has)
//!   fails, so a beancount upgrade that adds a check goes red here.
//!
//! The last two need Python with beancount (`python3`, or the interpreter
//! named by `RLEDGER_UPSTREAM_PYTHON`). Without it they print
//! [`SKIP_MARKER`] and pass; the `python-gated-cargo-tests` CI job installs
//! beancount and fails on that marker.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Printed when Python with beancount is unavailable; CI fails on it.
const SKIP_MARKER: &str = "Skipping: Python beancount not available";

const STATUSES: &[&str] = &["covered", "deviation", "not-applicable", "missing"];

fn fixtures() -> PathBuf {
    common::test_fixtures_dir().join("upstream-checks")
}

fn case_path(case: &str) -> PathBuf {
    fixtures().join("cases").join(format!("{case}.beancount"))
}

/// One row of the table, as the tests read it.
#[derive(Debug)]
struct Row {
    id: String,
    status: String,
    table: toml::Table,
}

impl Row {
    fn str(&self, key: &str) -> Option<&str> {
        self.table.get(key).and_then(toml::Value::as_str)
    }

    fn lines(&self, key: &str) -> Option<BTreeSet<i64>> {
        let value = self.table.get(key).or_else(|| self.table.get("lines"))?;
        let array = value
            .as_array()
            .unwrap_or_else(|| panic!("{}: `{key}` is not an array", self.id));
        Some(
            array
                .iter()
                .map(|v| {
                    v.as_integer()
                        .unwrap_or_else(|| panic!("{}: `{key}` holds a non-integer", self.id))
                })
                .collect(),
        )
    }

    fn python_crash(&self) -> bool {
        self.table
            .get("python_crash")
            .and_then(toml::Value::as_bool)
            .unwrap_or(false)
    }
}

fn rows() -> Vec<Row> {
    let path = fixtures().join("checks.toml");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
    let doc: toml::Table = text
        .parse()
        .unwrap_or_else(|e| panic!("parsing {}: {e}", path.display()));
    doc.get("check")
        .and_then(toml::Value::as_array)
        .expect("checks.toml has [[check]] rows")
        .iter()
        .map(|v| {
            let table = v.as_table().expect("[[check]] is a table").clone();
            let id = table
                .get("id")
                .and_then(toml::Value::as_str)
                .expect("every row has an id")
                .to_string();
            let status = table
                .get("status")
                .and_then(toml::Value::as_str)
                .unwrap_or_else(|| panic!("{id}: no status"))
                .to_string();
            Row { id, status, table }
        })
        .collect()
}

/// GitHub's anchor for a markdown heading.
fn slug(heading: &str) -> String {
    heading
        .trim()
        .to_lowercase()
        .chars()
        .filter(|c| c.is_alphanumeric() || *c == ' ' || *c == '-' || *c == '_')
        .map(|c| if c == ' ' { '-' } else { c })
        .collect()
}

#[test]
fn upstream_checks_table_is_well_formed() {
    let rows = rows();
    let root = common::project_root();
    let compat = std::fs::read_to_string(root.join("docs/reference/compatibility.md"))
        .expect("docs/reference/compatibility.md");
    let anchors: BTreeSet<String> = compat
        .lines()
        .filter_map(|l| l.strip_prefix('#'))
        .map(|l| slug(l.trim_start_matches('#')))
        .collect();

    let mut problems = Vec::new();
    let mut seen = BTreeSet::new();
    let mut cases_used = BTreeSet::new();
    for row in &rows {
        let id = &row.id;
        if !seen.insert(id.clone()) {
            problems.push(format!("{id}: listed twice"));
        }
        if !STATUSES.contains(&row.status.as_str()) {
            problems.push(format!("{id}: unknown status `{}`", row.status));
        }
        let has = |key: &str| row.str(key).is_some_and(|s| !s.trim().is_empty());
        match row.status.as_str() {
            "covered" => {
                if !has("rledger") {
                    problems.push(format!("{id}: covered, but no `rledger` says by what"));
                }
                if !has("case") && row.table.get("test").is_none() {
                    problems.push(format!("{id}: covered, but no `case` or `test` pins it"));
                }
            }
            "deviation" => match row.str("compat") {
                Some(link) => {
                    let anchor = link.strip_prefix("docs/reference/compatibility.md#");
                    if !anchor.is_some_and(|a| anchors.contains(a)) {
                        problems.push(format!(
                            "{id}: `compat` must link a heading of docs/reference/compatibility.md, got `{link}`"
                        ));
                    }
                }
                None => problems.push(format!("{id}: a deviation needs a `compat` link")),
            },
            "not-applicable" if !has("reason") => {
                problems.push(format!("{id}: not-applicable needs a `reason`"));
            }
            "missing" if !has("note") => {
                problems.push(format!(
                    "{id}: missing needs a `note` saying what rledger does"
                ));
            }
            _ => {}
        }
        if let Some(tests) = row.table.get("test") {
            for test in tests.as_array().into_iter().flatten() {
                let test = test.as_str().unwrap_or_default();
                let Some((file, name)) = test.split_once("::") else {
                    problems.push(format!("{id}: test `{test}` is not `path::function`"));
                    continue;
                };
                let source = std::fs::read_to_string(root.join(file)).unwrap_or_default();
                if !source.contains(&format!("fn {name}(")) {
                    problems.push(format!("{id}: test `{test}` does not exist"));
                }
            }
        }
        if let Some(case) = row.str("case") {
            cases_used.insert(case.to_string());
            if !case_path(case).exists() {
                problems.push(format!("{id}: case `{case}` has no file"));
            }
            let both = row.table.contains_key("lines");
            let split =
                row.table.contains_key("python_lines") || row.table.contains_key("rledger_lines");
            if both == split && !row.python_crash() {
                problems.push(format!(
                    "{id}: give either `lines` or both `python_lines` and `rledger_lines`"
                ));
            }
            if row.python_crash()
                && (both
                    || row.table.contains_key("python_lines")
                    || !row.table.contains_key("rledger_lines"))
            {
                problems.push(format!("{id}: python_crash rows give `rledger_lines` only"));
            }
            let differs =
                row.python_crash() || row.lines("python_lines") != row.lines("rledger_lines");
            if row.status == "covered" && differs && !has("note") {
                problems.push(format!(
                    "{id}: covered on different lines in the two tools; a `note` must say how"
                ));
            }
        } else if [
            "lines",
            "python_lines",
            "rledger_lines",
            "code",
            "python_message",
        ]
        .iter()
        .any(|k| row.table.contains_key(*k))
        {
            problems.push(format!("{id}: line fields without a `case`"));
        }
    }
    for entry in std::fs::read_dir(fixtures().join("cases")).expect("cases dir") {
        let path = entry.expect("dir entry").path();
        if path.extension().is_some_and(|e| e == "beancount") {
            let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
            if !cases_used.contains(&stem) {
                problems.push(format!("case `{stem}` is used by no row"));
            }
        }
    }
    assert!(
        problems.is_empty(),
        "checks.toml:\n  {}",
        problems.join("\n  ")
    );
}

/// Run `job` over `items` on a few threads, keeping the input order.
fn parallel<T: Sync, R: Send>(items: &[T], job: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let next = AtomicUsize::new(0);
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get().min(8));
    let mut results: Vec<(usize, R)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    let mut out = Vec::new();
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        let Some(item) = items.get(i) else { break };
                        out.push((i, job(item)));
                    }
                    out
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("worker panicked"))
            .collect()
    });
    results.sort_by_key(|(i, _)| *i);
    results.into_iter().map(|(_, r)| r).collect()
}

/// The distinct cases the rows use.
fn cases(rows: &[Row]) -> Vec<String> {
    rows.iter()
        .filter_map(|r| r.str("case").map(str::to_string))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

#[test]
fn upstream_checks_rledger_matches_the_table() {
    let rledger = require_rledger!();
    let rows = rows();
    let names = cases(&rows);
    let config = tempfile::tempdir().expect("tempdir");
    let outputs: BTreeMap<String, serde_json::Value> = names
        .iter()
        .cloned()
        .zip(parallel(&names, |case| {
            let out = Command::new(&rledger)
                .args(["check", "--no-cache", "--format", "json"])
                .arg(case_path(case))
                .env("RLEDGER_CONFIG_DIR", config.path())
                .env("NO_COLOR", "1")
                .output()
                .expect("run rledger");
            serde_json::from_slice(&out.stdout).unwrap_or_else(|e| {
                panic!(
                    "{case}: rledger's JSON did not parse ({e}):\n{}{}",
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                )
            })
        }))
        .collect();

    let mut problems = Vec::new();
    for row in &rows {
        let Some(case) = row.str("case") else {
            continue;
        };
        let diagnostics = outputs[case]["diagnostics"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        let errors: Vec<_> = diagnostics
            .iter()
            .filter(|d| d["severity"] == "error")
            .collect();
        let expected = row.lines("rledger_lines").unwrap_or_default();
        let code = row.str("code").unwrap_or_default();
        let found: BTreeSet<i64> = if code.is_empty() {
            errors.iter().filter_map(|d| d["line"].as_i64()).collect()
        } else {
            errors
                .iter()
                // `E8004|E8005`: any of these. A code can depend on the
                // build's features (a Python module name is E8004 with the
                // Python runtime compiled in, E8005 without it).
                .filter(|d| code.split('|').any(|c| d["code"] == c))
                .filter_map(|d| d["line"].as_i64())
                .collect()
        };
        if found != expected {
            problems.push(format!(
                "{}: case {case}: rledger reports {} on lines {found:?}, the table says {expected:?}\n    {}",
                row.id,
                if code.is_empty() { "errors" } else { code },
                serde_json::to_string(&errors).unwrap_or_default()
            ));
        }
    }
    assert!(
        problems.is_empty(),
        "rledger disagrees with checks.toml (update the row, or fix the regression):\n  {}",
        problems.join("\n  ")
    );
}

/// The interpreter with beancount, or `None` after printing [`SKIP_MARKER`].
fn python() -> Option<String> {
    let python = std::env::var("RLEDGER_UPSTREAM_PYTHON").unwrap_or_else(|_| "python3".into());
    let ok = Command::new(&python)
        .args(["-I", "-c", "import beancount.scripts.check"])
        .output()
        .is_ok_and(|o| o.status.success());
    if ok {
        Some(python)
    } else {
        eprintln!("{SKIP_MARKER}");
        None
    }
}

/// Whether `message` matches beancount's `template`: its literal parts
/// appear in order (`{}` stands for any text). A search, not an anchored
/// match, since beancount wraps some messages ("Error for option ...: ").
fn matches_template(message: &str, template: &str) -> bool {
    let mut rest = message;
    for part in template.split("{}") {
        match rest.find(part) {
            Some(at) => rest = &rest[at + part.len()..],
            None => return false,
        }
    }
    true
}

/// How a row recognizes its own message among beancount's errors.
fn python_matcher(row: &Row) -> Box<dyn Fn(&str) -> bool + '_> {
    if let Some(needle) = row.str("python_message") {
        return Box::new(move |m: &str| m.contains(needle));
    }
    let (kind, rest) = row.id.split_once(':').unwrap_or_default();
    if matches!(kind, "site" | "raise")
        && let Some((_, template)) = rest.split_once(':')
        && template != "<dynamic>"
    {
        let template = template.replace("\\n", "\n");
        return Box::new(move |m: &str| matches_template(m, &template));
    }
    Box::new(|_| true)
}

#[test]
fn upstream_checks_beancount_matches_the_table() {
    let Some(python) = python() else { return };
    let rows = rows();
    let names = cases(&rows);
    let outputs: BTreeMap<String, (bool, String)> = names
        .iter()
        .cloned()
        .zip(parallel(&names, |case| {
            let scratch = tempfile::tempdir().expect("tempdir");
            let out = Command::new(&python)
                .args([
                    "-I",
                    "-m",
                    "beancount.scripts.check",
                    "--json",
                    "--no-cache",
                ])
                .arg(case_path(case))
                .current_dir(scratch.path())
                .output()
                .expect("run bean-check");
            let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
            (
                stderr.contains("Traceback (most recent call last)") && out.stdout.is_empty(),
                format!("{}{stderr}", String::from_utf8_lossy(&out.stdout)),
            )
        }))
        .collect();

    let mut problems = Vec::new();
    for row in &rows {
        let Some(case) = row.str("case") else {
            continue;
        };
        let (crashed, text) = &outputs[case];
        if row.python_crash() {
            if !crashed {
                problems.push(format!(
                    "{}: case {case}: the table says bean-check crashes, and it no longer does:\n    {text}",
                    row.id
                ));
            }
            continue;
        }
        let errors: Vec<serde_json::Value> = serde_json::from_str::<serde_json::Value>(text)
            .ok()
            .and_then(|v| v["errors"].as_array().cloned())
            .unwrap_or_else(|| {
                problems.push(format!(
                    "{}: case {case}: bean-check gave no JSON:\n    {text}",
                    row.id
                ));
                Vec::new()
            });
        let matcher = python_matcher(row);
        let found: BTreeSet<i64> = errors
            .iter()
            .filter(|e| matcher(e["message"].as_str().unwrap_or_default()))
            .filter_map(|e| e["lineno"].as_i64())
            .collect();
        let expected = row.lines("python_lines").unwrap_or_default();
        if found != expected {
            problems.push(format!(
                "{}: case {case}: bean-check reports it on lines {found:?}, the table says {expected:?}\n    {}",
                row.id,
                serde_json::to_string(&errors).unwrap_or_default()
            ));
        }
    }
    assert!(
        problems.is_empty(),
        "bean-check disagrees with checks.toml:\n  {}",
        problems.join("\n  ")
    );
}

#[test]
fn upstream_checks_table_lists_every_upstream_check() {
    let Some(python) = python() else { return };
    let script = fixtures().join("enumerate.py");
    let out = Command::new(&python)
        .arg("-I")
        .arg(&script)
        .output()
        .expect("run enumerate.py");
    assert!(
        out.status.success(),
        "enumerate.py failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let upstream: BTreeSet<String> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::to_string)
        .collect();
    let version = Command::new(&python)
        .args(["-I", "-c", "import beancount; print(beancount.__version__)"])
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default();
    let table: BTreeSet<String> = rows()
        .into_iter()
        .map(|r| r.id)
        .filter(|id| !id.starts_with("manual:"))
        .collect();
    let untracked: Vec<_> = upstream.difference(&table).collect();
    let stale: Vec<_> = table.difference(&upstream).collect();
    assert!(
        untracked.is_empty() && stale.is_empty(),
        "checks.toml is out of step with beancount {version} ({}):\n\
         checks beancount has that the table does not (add a row: what does rledger do?):\n  {}\n\
         rows for checks beancount no longer has (remove or re-key them):\n  {}",
        script.display(),
        untracked
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n  "),
        stale
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n  "),
    );
}

#[test]
fn test_matches_template_reads_placeholders_as_any_text() {
    assert!(matches_template(
        "Duplicate open directive for Assets:Cash",
        "Duplicate open directive for {}"
    ));
    assert!(matches_template(
        "Error for option 'x': Invalid value 'y'",
        "Invalid value '{}'"
    ));
    assert!(!matches_template(
        "Duplicate close directive for Assets:Cash",
        "Duplicate open directive for {}"
    ));
    assert!(!matches_template("b then a", "a{}b"));
}
